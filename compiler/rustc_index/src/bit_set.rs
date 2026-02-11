use std::alloc::{Layout, alloc, alloc_zeroed, dealloc, handle_alloc_error, realloc};
use std::marker::PhantomData;
#[cfg(not(feature = "nightly"))]
use std::mem;
use std::mem::ManuallyDrop;
use std::ops::{BitAnd, BitAndAssign, BitOrAssign, Bound, Not, Range, RangeBounds, Shl};
use std::ptr::NonNull;
use std::rc::Rc;
use std::{fmt, iter, slice};

use Chunk::*;
use either::Either;
#[cfg(feature = "nightly")]
use rustc_macros::{Decodable_NoContext, Encodable_NoContext};
use rustc_serialize::{Decodable, Decoder, Encodable, Encoder};

use crate::{Idx, IndexVec};

#[cfg(test)]
mod tests;

type Word = u64;
const WORD_BYTES: usize = size_of::<Word>();
const WORD_BITS: usize = WORD_BYTES * 8;

// The choice of chunk size has some trade-offs.
//
// A big chunk size tends to favour cases where many large `ChunkedBitSet`s are
// present, because they require fewer `Chunk`s, reducing the number of
// allocations and reducing peak memory usage. Also, fewer chunk operations are
// required, though more of them might be `Mixed`.
//
// A small chunk size tends to favour cases where many small `ChunkedBitSet`s
// are present, because less space is wasted at the end of the final chunk (if
// it's not full).
const CHUNK_WORDS: usize = 32;
const CHUNK_BITS: usize = CHUNK_WORDS * WORD_BITS; // 2048 bits

/// ChunkSize is small to keep `Chunk` small. The static assertion ensures it's
/// not too small.
type ChunkSize = u16;
const _: () = assert!(CHUNK_BITS <= ChunkSize::MAX as usize);

pub trait BitRelations<Rhs> {
    fn union(&mut self, other: &Rhs) -> bool;
    fn subtract(&mut self, other: &Rhs) -> bool;
    fn intersect(&mut self, other: &Rhs) -> bool;
}

#[inline]
fn inclusive_start_end<T: Idx>(
    range: impl RangeBounds<T>,
    domain: usize,
) -> Option<(usize, usize)> {
    // Both start and end are inclusive.
    let start = match range.start_bound().cloned() {
        Bound::Included(start) => start.index(),
        Bound::Excluded(start) => start.index() + 1,
        Bound::Unbounded => 0,
    };
    let end = match range.end_bound().cloned() {
        Bound::Included(end) => end.index(),
        Bound::Excluded(end) => end.index().checked_sub(1)?,
        Bound::Unbounded => domain - 1,
    };
    assert!(end < domain);
    if start > end {
        return None;
    }
    Some((start, end))
}

macro_rules! bit_relations_inherent_impls {
    () => {
        /// Sets `self = self | other` and returns `true` if `self` changed
        /// (i.e., if new bits were added).
        pub fn union<Rhs>(&mut self, other: &Rhs) -> bool
        where
            Self: BitRelations<Rhs>,
        {
            <Self as BitRelations<Rhs>>::union(self, other)
        }

        /// Sets `self = self - other` and returns `true` if `self` changed.
        /// (i.e., if any bits were removed).
        pub fn subtract<Rhs>(&mut self, other: &Rhs) -> bool
        where
            Self: BitRelations<Rhs>,
        {
            <Self as BitRelations<Rhs>>::subtract(self, other)
        }

        /// Sets `self = self & other` and return `true` if `self` changed.
        /// (i.e., if any bits were removed).
        pub fn intersect<Rhs>(&mut self, other: &Rhs) -> bool
        where
            Self: BitRelations<Rhs>,
        {
            <Self as BitRelations<Rhs>>::intersect(self, other)
        }
    };
}

/// A fixed-size bitset type with a dense representation, using only one [`Word`] on the stack.
///
/// This bit set occupies only a single [`Word`] of stack space. It can represent a domain size
/// of up to `[WORD_BITS] - 1` directly inline. If the domain size exceeds this limit, it instead
/// becomes a pointer to a sequence of [`Word`]s on the heap. This makes it very efficient for
/// domain sizes smaller than `[WORD_BITS]`.
///
/// Additionally, if the set does not fit in one [`Word`], there is a special inline
/// variant for the empty set. In this case, the domain size is stored inline along with a few
/// bits indicating that the set is empty. Allocation is deferred until needed, such as on
/// the first insert or remove operation. This avoids the need to wrap a lazily initialised bit set
/// in a [`OnceCell`](std::cell::OnceCell) or an [`Option`]—you can simply create an empty set and
/// populate it if needed.
///
/// Note 1: Since this bitset is dense, if your domain is large and/or relatively homogeneous (e.g.
/// long runs of set or unset bits), it may be more efficient to use a
/// [`MixedBitSet`](crate::bit_set::MixedBitSet) or an
/// [`IntervalSet`](crate::interval::IntervalSet), which are better suited for sparse or highly
/// compressible domains.
///
/// Note 2: Use [`GrowableBitSet`] if you require support for resizing after creation.
///
/// `T` is an index type—typically a newtyped `usize` wrapper, but it may also simply be `usize`.
///
/// Any operation involving an element may panic if the element is equal to or greater than the
/// domain size. Operations involving two bitsets may panic if their domain sizes differ. Panicking
/// is not garranteed though as we store the domain size rounded up to the next multiple of
/// [`WORD_BITS`].
#[cfg(feature = "nightly")]
pub union DenseBitSet<T> {
    /// The bit set fits in a single [`Word`] stored inline on the stack.
    ///
    /// The most significant bit is set to 1 to distinguish this from the other variants. You
    /// must never change that "tag bit" after the bit set has been created.
    ///
    /// The remaining bits makes up the bit set. The exact domain size is not stored.
    inline: Word,

    /// The bit set doesn't fit in a single word, but is empty and not yet allocated.
    ///
    /// The first (most significant) two bits are set to `[0, 1]` to distinguish this variant
    /// from others. This tag is stored in [`Self::EMPTY_UNALLOCATED_TAG_BITS`]. The remaining bits
    /// hold the domain size (capacity) **in words** of the set, which is needed if the set is
    /// eventually allocated.
    ///
    /// Note that because the capacity is stored in words, not in bits, there is plenty of room
    /// for the two tag bits.
    empty_unallocated: usize,

    /// The bit set is stored on the heap.
    ///
    /// The two most significant bits are set to zero if this field is active.
    on_heap: ManuallyDrop<BitSetOnHeap>,

    marker: PhantomData<T>,
}

/// A pointer to a dense bit set stored on the heap.
///
/// This struct is a `usize`, with its two most significant bits always set to 0. If the value is
/// shifted left by 2 bits, it yields a pointer to a sequence of words on the heap. The first word
/// in this sequence represents the length—it indicates how many words follow. These subsequent
/// words make up the actual bit set.
///
/// For example, suppose the bit set should support a domain size of 240 bits. We first determine
/// how many words are needed to store 240 bits—that’s 4 words, assuming `[WORD_BITS] == 64`.
/// The pointer in this struct then points to a sequence of five words allocated on the heap. The
/// first word has the value 4 (the length), and the remaining four words comprise the bit set.
#[repr(transparent)]
struct BitSetOnHeap(usize);

impl BitSetOnHeap {
    fn new_empty(len: usize) -> Self {
        debug_assert!(len >= 1);

        // The first word is used to store the total number of words. The rest of the words
        // store the bits.
        let num_words = len + 1;

        let layout = Layout::array::<Word>(num_words).expect("Bit set too large");
        // SAFETY: `num_words` is always at least `1` so we never allocate zero size.
        let ptr = unsafe { alloc_zeroed(layout).cast::<Word>() };
        let Some(ptr) = NonNull::<Word>::new(ptr) else {
            handle_alloc_error(layout);
        };

        // Store the length in the first word.
        unsafe { ptr.write(len as Word) };

        // Convert `ptr` to a `usize` and shift it two bits to the right.
        BitSetOnHeap((ptr.as_ptr() as usize) >> 2)
    }

    /// Get a slice with all bits in this bit set.
    ///
    /// Note that the number of bits in the set is rounded up to the next power of `Usize::BITS`. So
    /// if the user requested a domain_size of 216 bits, a slice with 4 words will be returned on a
    /// 64-bit machine.
    #[inline]
    fn as_slice(&self) -> &[Word] {
        let ptr = (self.0 << 2) as *const Word;
        let len = unsafe { ptr.read() } as usize;
        // The slice starts at the second word.
        unsafe { slice::from_raw_parts(ptr.add(1), len) }
    }

    /// Get a mutable slice with all bits in this bit set.
    ///
    /// Note that the number of bits in the set is rounded up to the next power of `Usize::BITS`. So
    /// if the user requested a domain_size of 216 bits, a slice with 4 words will be returned on a
    /// 64-bit machine.
    #[inline]
    fn as_mut_slice(&mut self) -> &mut [Word] {
        let ptr = (self.0 << 2) as *mut Word;
        let len = unsafe { ptr.read() } as usize;
        // The slice starts at the second word.
        unsafe { slice::from_raw_parts_mut(ptr.add(1), len) }
    }

    /// Check if the set is empty.
    fn is_empty(&self) -> bool {
        self.as_slice().iter().all(|&x| x == 0)
    }

    /// Get the number of words.
    #[allow(dead_code)] // FIXME
    #[inline]
    fn n_words(&self) -> Word {
        let ptr = (self.0 << 2) as *const Word;
        unsafe { ptr.read() }
    }

    /// Get the capacity, that is the number of elements that can be stored in this set.
    fn capacity(&self) -> usize {
        let ptr = (self.0 << 2) as *const Word;
        let len = unsafe { ptr.read() } as usize;
        len * WORD_BITS
    }

    /// Make sure the set can hold at least `min_domain_size` elements. Reallocate if necessary.
    fn ensure_capacity(&mut self, min_domain_size: usize) {
        let len = min_domain_size.div_ceil(WORD_BITS);

        let old_ptr = (self.0 << 2) as *const Word;
        let old_len = unsafe { old_ptr.read() } as usize;

        if len <= old_len {
            return;
        }

        // The first word is used to store the total number of words. The rest of the words
        // store the bits.
        let num_words = len + 1;
        let old_num_words = old_len + 1;

        let new_layout = Layout::array::<Word>(num_words).expect("Bit set too large");
        let old_layout = Layout::array::<usize>(old_num_words).expect("Bit set too large");

        // SAFETY: `num_words` is always at least `1` so we never allocate zero size.
        let ptr =
            unsafe { realloc(old_ptr as *mut u8, old_layout, new_layout.size()).cast::<Word>() };
        let Some(ptr) = NonNull::<Word>::new(ptr) else {
            handle_alloc_error(new_layout);
        };

        // Store the length in the first word.
        unsafe { ptr.write(len as Word) };

        // Set all the new words to 0.
        for word_idx in old_num_words..num_words {
            unsafe { ptr.add(word_idx).write(0x0) }
        }

        // Convert `ptr` to a `usize` and shift it two bits to the right.
        self.0 = (ptr.as_ptr() as usize) >> 2
    }
}

impl Clone for BitSetOnHeap {
    fn clone(&self) -> Self {
        let ptr = (self.0 << 2) as *const Word;
        let len = unsafe { ptr.read() } as usize;
        let num_words = len + 1;

        let layout = Layout::array::<usize>(num_words).expect("Bit set too large");
        // SAFETY: `num_words` is always at least `1` so we never allocate zero size.
        let new_ptr = unsafe { alloc(layout).cast::<Word>() };
        let Some(new_ptr) = NonNull::<Word>::new(new_ptr) else {
            handle_alloc_error(layout);
        };

        unsafe { ptr.copy_to_nonoverlapping(new_ptr.as_ptr(), num_words) };

        BitSetOnHeap((new_ptr.as_ptr() as usize) >> 2)
    }
}

impl Drop for BitSetOnHeap {
    fn drop(&mut self) {
        let ptr = (self.0 << 2) as *mut Word;

        // SAFETY: The first word stores the number of words for the bit set. We have to add 1
        // because the first word storing the length is allocated as well.
        let num_words = unsafe { ptr.read() } as usize + 1;
        let layout = Layout::array::<Word>(num_words).expect("Bit set too large");
        // SAFETY: We know that `on_heap` has been allocated with the same layout. See the
        // `new` method for reference.
        unsafe { dealloc(ptr.cast::<u8>(), layout) };
    }
}

impl<T: Idx> DenseBitSet<T> {
    /// The maximum domain size that could be stored inlined on the stack.
    pub const INLINE_CAPACITY: usize = WORD_BITS - 1;

    /// A [`Word`] with the most significant bit set. That is the tag bit telling that the set is
    /// inlined.
    const IS_INLINE_TAG_BIT: Word = 0x1 << (WORD_BITS - 1);

    /// The tag for the `empty_unallocated` variant. The two most significant bits are
    /// `[0, 1]`.
    const EMPTY_UNALLOCATED_TAG_BITS: usize = 0b01 << (usize::BITS - 2);

    /// Creates a new, empty bitset with a given `domain_size`.
    ///
    /// If `domain_size` is <= [`Self::INLINE_CAPACITY`], then it is stored inline on the stack,
    /// otherwise it is stored on the heap.
    #[inline]
    pub fn new_empty(domain_size: usize) -> DenseBitSet<T> {
        if domain_size <= Self::INLINE_CAPACITY {
            // The first bit is set to indicate the union variant.
            Self { inline: Self::IS_INLINE_TAG_BIT }
        } else {
            let num_words = domain_size.div_ceil(WORD_BITS);
            debug_assert!(num_words.leading_zeros() >= 2);
            Self { empty_unallocated: Self::EMPTY_UNALLOCATED_TAG_BITS | num_words }
        }
    }

    /// Creates a new, filled bitset with a given `domain_size`.
    #[inline]
    pub fn new_filled(domain_size: usize) -> DenseBitSet<T> {
        if domain_size <= Self::INLINE_CAPACITY {
            Self {
                inline: Word::MAX.unbounded_shr((WORD_BITS - domain_size) as u32)
                    | Self::IS_INLINE_TAG_BIT,
            }
        } else {
            let num_words = domain_size.div_ceil(WORD_BITS);
            let mut on_heap = BitSetOnHeap::new_empty(num_words);
            let words = on_heap.as_mut_slice();
            for word in words.iter_mut() {
                *word = Word::MAX;
            }
            // Remove excessive bits on the last word.
            // Trust me: this mask is correct.
            let last_word_mask = Word::MAX.wrapping_shr(domain_size.wrapping_neg() as u32);
            *words.last_mut().unwrap() &= last_word_mask;
            Self { on_heap: ManuallyDrop::new(on_heap) }
        }
    }

    /// Check if `self` is inlined.
    /// If this function returns `true`, it is safe to assume `self.inline`. Else, it is safe to
    /// assume `self.empty_unallocated`, or `self.on_heap`.
    #[inline(always)]
    pub fn is_inline(&self) -> bool {
        // We check if the first bit is set. If so, it is inlined, otherwise it is on the heap.
        (unsafe { self.inline } & Self::IS_INLINE_TAG_BIT) != 0
    }

    /// Check if `self` has a too large domain to be stored inline, is empty, and is not yet
    /// allocated.
    // If this function returns `true`, it is safe to assume `self.empty_unallocated`. Else, it is
    // safe to assume `self.inline`, or `self.on_heap`.
    #[inline(always)]
    pub const fn is_empty_unallocated(&self) -> bool {
        const MASK: usize = usize::MAX << usize::BITS - 2;
        (unsafe { self.empty_unallocated } & MASK) == Self::EMPTY_UNALLOCATED_TAG_BITS
    }

    /// Check if `self` is `empty_unallocated` and if so return the number of words required to
    /// store the expected capacity.
    // If this function returns `true`, it is safe to assume `self.empty_unallocated`. Else, it is
    // safe to assume `self.inline`, or `self.on_heap`.
    #[inline(always)]
    pub const fn empty_unallocated_get_num_words(&self) -> Option<usize> {
        if self.is_empty_unallocated() {
            Some(unsafe { self.empty_unallocated } ^ Self::EMPTY_UNALLOCATED_TAG_BITS)
        } else {
            None
        }
    }

    /// Check if `self` is allocated on the heap and return a reference to it in that case.
    fn on_heap(&self) -> Option<&BitSetOnHeap> {
        let self_word = unsafe { self.inline };
        // Check if the two most significant bits are 0.
        if self_word & Word::MAX >> 2 == self_word { Some(unsafe { &self.on_heap }) } else { None }
    }

    /// Check if `self` is allocated on the heap and return a mutable reference to it in that case.
    fn on_heap_mut(&mut self) -> Option<&mut ManuallyDrop<BitSetOnHeap>> {
        let self_word = unsafe { self.inline };
        // Check if the two most significant bits are 0.
        if self_word & Word::MAX >> 2 == self_word {
            Some(unsafe { &mut self.on_heap })
        } else {
            None
        }
    }

    /// If `self` is `empty_unallocated`, allocate it, otherwise return `self.on_heap_mut()`.
    fn on_heap_get_or_alloc(&mut self) -> &mut BitSetOnHeap {
        if let Some(num_words) = self.empty_unallocated_get_num_words() {
            *self = Self { on_heap: ManuallyDrop::new(BitSetOnHeap::new_empty(num_words)) };
            unsafe { &mut self.on_heap }
        } else {
            self.on_heap_mut().unwrap()
        }
    }

    /// Clear all elements.
    #[inline]
    pub fn clear(&mut self) {
        if self.is_inline() {
            self.inline = Self::IS_INLINE_TAG_BIT
        } else if let Some(on_heap) = self.on_heap_mut() {
            for word in on_heap.as_mut_slice() {
                *word = 0x0;
            }
        }
    }

    /// Get an iterator of all words making up the set.
    pub(super) fn words(&self) -> impl ExactSizeIterator<Item = Word> {
        if self.is_inline() {
            let word = unsafe { self.inline } ^ Self::IS_INLINE_TAG_BIT;
            Either::Left(iter::once(word))
        } else if let Some(num_words) = self.empty_unallocated_get_num_words() {
            Either::Right(Either::Left(iter::repeat_n(0, num_words)))
        } else {
            Either::Right(Either::Right(self.on_heap().unwrap().as_slice().iter().copied()))
        }
    }

    /// Count the number of set bits in the set.
    #[inline]
    pub fn count(&self) -> usize {
        if self.is_inline() {
            let x = unsafe { self.inline };
            x.count_ones() as usize - 1
        } else if self.is_empty_unallocated() {
            0
        } else {
            self.on_heap().unwrap().as_slice().iter().map(|w| w.count_ones() as usize).sum()
        }
    }

    /// Returns `true` if `self` contains `elem`.
    #[inline]
    pub fn contains(&self, elem: T) -> bool {
        // Check if the `i`th bit is set in a word.
        let contains_bit = |word: Word, bit_idx: u32| {
            let mask = 0x01 << bit_idx;
            (word & mask) != 0
        };

        let idx = elem.index();
        if self.is_inline() {
            let x = unsafe { self.inline };
            debug_assert!(idx < Self::INLINE_CAPACITY, "index too large: {idx}");
            contains_bit(x, idx as u32)
        } else if let Some(on_heap) = self.on_heap() {
            let word_idx = idx / WORD_BITS;
            let bit_idx = (idx % WORD_BITS) as u32;
            let word = on_heap.as_slice()[word_idx];
            contains_bit(word, bit_idx)
        } else {
            debug_assert!(self.is_empty_unallocated());
            false
        }
    }

    /// Is `self` is a (non-strict) superset of `other`?
    ///
    /// May panic if `self` and other have different sizes.
    #[inline]
    pub fn superset(&self, other: &DenseBitSet<T>) -> bool {
        // Function to check that a usize is a superset of another.
        let word_is_superset = |x: Word, other: Word| (!x & other) == 0;

        if self.is_inline() {
            let x = unsafe { self.inline };
            assert!(other.is_inline(), "bit sets has different domain sizes");
            let y = unsafe { other.inline };
            word_is_superset(x, y)
        } else if other.is_empty_unallocated() {
            true
        } else {
            let other_on_heap = other.on_heap().unwrap();
            if self.is_empty_unallocated() {
                other_on_heap.is_empty()
            } else {
                let on_heap = self.on_heap().unwrap();
                let self_slice = on_heap.as_slice();
                let other_slice = other_on_heap.as_slice();
                debug_assert_eq!(
                    self_slice.len(),
                    other_slice.len(),
                    "bit sets have different domain sizes"
                );
                self_slice.iter().zip(other_slice).all(|(&x, &y)| (!x & y) == 0)
            }
        }
    }

    /// Returns an iterator over the indices for all elements in this set.
    #[inline(always)]
    pub fn iter_usizes(&self) -> BitIter<'_, usize> {
        if self.is_inline() {
            let x = unsafe { self.inline };
            // Remove the tag bit.
            let without_tag_bit = x ^ Self::IS_INLINE_TAG_BIT;
            BitIter::from_single_word(without_tag_bit)
        } else if let Some(on_heap) = self.on_heap() {
            BitIter::from_slice(on_heap.as_slice())
        } else {
            debug_assert!(self.is_empty_unallocated());
            BitIter::from_single_word(0)
        }
    }

    /// Is the set empty?
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.as_slice().iter().all(|&x| x == 0)
    }

    /// Insert `elem`. Returns whether the set has changed.
    #[inline]
    pub fn insert(&mut self, elem: T) -> bool {
        assert!(
            elem.index() < self.domain_size,
            "inserting element at index {} but domain size is {}",
            elem.index(),
            self.domain_size,
        );
        let (word_index, mask) = word_index_and_mask(elem);
        let word_ref = &mut self.words[word_index];
        let word = *word_ref;
        let new_word = word | mask;
        *word_ref = new_word;
        new_word != word
    }

    #[inline]
    pub fn insert_range(&mut self, elems: impl RangeBounds<T>) {
        let Some((start, end)) = inclusive_start_end(elems, self.domain_size) else {
            return;
        };

        let (start_word_index, start_mask) = word_index_and_mask(start);
        let (end_word_index, end_mask) = word_index_and_mask(end);

        // Set all words in between start and end (exclusively of both).
        for word_index in (start_word_index + 1)..end_word_index {
            self.words[word_index] = !0;
        }

        if start_word_index != end_word_index {
            // Start and end are in different words, so we handle each in turn.
            //
            // We set all leading bits. This includes the start_mask bit.
            self.words[start_word_index] |= !(start_mask - 1);
            // And all trailing bits (i.e. from 0..=end) in the end word,
            // including the end.
            self.words[end_word_index] |= end_mask | (end_mask - 1);
        } else {
            self.words[start_word_index] |= end_mask | (end_mask - start_mask);
        }
    }

    /// Sets all bits to true.
    pub fn insert_all(&mut self, domain_size: usize) {
        if self.is_inline() {
            debug_assert!(domain_size <= Self::INLINE_CAPACITY);
            unsafe {
                self.inline |= Word::MAX.unbounded_shr(WORD_BITS as u32 - domain_size as u32)
            };
        } else {
            let on_heap = self.on_heap_get_or_alloc();
            debug_assert!(on_heap.capacity() >= domain_size, "domain size too big");
            let words = on_heap.as_mut_slice();

            let (end_word_index, end_mask) = word_index_and_mask(domain_size - 1);

            for word_index in 0..end_word_index {
                words[word_index] = Word::MAX;
            }

            words[end_word_index] |= end_mask | (end_mask - 1);
        }
    }

    /// Checks whether any bit in the given range is a 1.
    #[inline]
    pub fn contains_any(&self, elems: impl RangeBounds<T>) -> bool {
        let Some((start, end)) = inclusive_start_end(elems, self.domain_size) else {
            return false;
        };
        let (start_word_index, start_mask) = word_index_and_mask(start);
        let (end_word_index, end_mask) = word_index_and_mask(end);

        if start_word_index == end_word_index {
            self.words[start_word_index] & (end_mask | (end_mask - start_mask)) != 0
        } else {
            if self.words[start_word_index] & !(start_mask - 1) != 0 {
                return true;
            }

            let remaining = start_word_index + 1..end_word_index;
            if remaining.start <= remaining.end {
                self.words[remaining].iter().any(|&w| w != 0)
                    || self.words[end_word_index] & (end_mask | (end_mask - 1)) != 0
            } else {
                false
            }
        }
    }

    /// Returns `true` if the set has changed.
    #[inline]
    pub fn remove(&mut self, elem: T) -> bool {
        assert!(elem.index() < self.domain_size);
        let (word_index, mask) = word_index_and_mask(elem);
        let word_ref = &mut self.words[word_index];
        let word = *word_ref;
        let new_word = word & !mask;
        *word_ref = new_word;
        new_word != word
    }

    /// Iterates over the indices of set bits in a sorted order.
    #[inline]
    pub fn iter(&self) -> BitIter<'_, T> {
        if self.is_inline() {
            let x = unsafe { self.inline };
            // Remove the tag bit.
            let without_tag_bit = x ^ Self::IS_INLINE_TAG_BIT;
            BitIter::from_single_word(without_tag_bit)
        } else if let Some(on_heap) = self.on_heap() {
            BitIter::from_slice(on_heap.as_slice())
        } else {
            debug_assert!(self.is_empty_unallocated());
            BitIter::from_single_word(0)
        }
    }

    pub fn last_set_in(&self, range: impl RangeBounds<T>) -> Option<T> {
        let (start, end) = inclusive_start_end(range, self.domain_size)?;
        let (start_word_index, _) = word_index_and_mask(start);
        let (end_word_index, end_mask) = word_index_and_mask(end);

        let end_word = self.words[end_word_index] & (end_mask | (end_mask - 1));
        if end_word != 0 {
            let pos = max_bit(end_word) + WORD_BITS * end_word_index;
            if start <= pos {
                return Some(T::new(pos));
            }
        }

        // We exclude end_word_index from the range here, because we don't want
        // to limit ourselves to *just* the last word: the bits set it in may be
        // after `end`, so it may not work out.
        if let Some(offset) =
            self.words[start_word_index..end_word_index].iter().rposition(|&w| w != 0)
        {
            let word_idx = start_word_index + offset;
            let start_word = self.words[word_idx];
            let pos = max_bit(start_word) + WORD_BITS * word_idx;
            if start <= pos {
                return Some(T::new(pos));
            }
        }

        None
    }

    bit_relations_inherent_impls! {}

    /// Sets `self = self | !other` for all elements less than `domain_size`.
    ///
    /// FIXME: Incorporate this into [`BitRelations`] and fill out
    /// implementations for other bitset types, if needed.
    pub fn union_not(&mut self, other: &DenseBitSet<T>, domain_size: usize) {
        if self.is_inline() {
            assert!(other.is_inline());

            let self_word = unsafe { &mut self.inline };
            let other_word = unsafe { other.inline };

            debug_assert!(domain_size <= Self::INLINE_CAPACITY);

            *self_word |= !other_word & Word::MAX.unbounded_shr((WORD_BITS - domain_size) as u32);
        } else if other.is_empty_unallocated() {
            self.insert_all(domain_size);
        } else {
            let self_words = self.on_heap_get_or_alloc().as_mut_slice();
            let other_words = other.on_heap().unwrap().as_slice();

            // Set all but the last word if domain_size is not divisible by `WORD_BITS`.
            for (self_word, other_word) in
                self_words.iter_mut().zip(other_words).take(domain_size / WORD_BITS)
            {
                *self_word |= !other_word;
            }

            let remaining_bits = domain_size % WORD_BITS;
            if remaining_bits > 0 {
                let last_idx = domain_size / WORD_BITS;
                self_words[last_idx] |= !other_words[last_idx] & !(Word::MAX << remaining_bits);
            }
        }
    }
}

// dense REL dense
impl<T: Idx> BitRelations<DenseBitSet<T>> for DenseBitSet<T> {
    fn union(&mut self, other: &DenseBitSet<T>) -> bool {
        if self.is_empty_unallocated() {
            debug_assert!(!other.is_inline());
            *self = other.clone();
            !self.is_empty()
        } else if other.is_empty_unallocated() {
            false
        } else {
            // SAFETY: The union operation does not remove any bit set to 1, so the tag bit is
            // unaffected.
            unsafe { self.binary_operation(other, |x, y| *x |= y) }
        }
    }

    fn subtract(&mut self, other: &DenseBitSet<T>) -> bool {
        if self.is_empty_unallocated() || other.is_empty_unallocated() {
            false
        } else {
            unsafe { self.binary_operation_safe(other, |x, y| *x &= !y) }
        }
    }

    fn intersect(&mut self, other: &DenseBitSet<T>) -> bool {
        if self.is_empty_unallocated() {
            false
        } else if other.is_empty_unallocated() {
            debug_assert!(!self.is_inline());
            let was_empty = self.is_empty();
            self.clear();
            !was_empty
        } else {
            // SAFETY: Since the tag bit is set in both `self` and `other`, the intersection won't
            // remove it.
            unsafe { self.binary_operation(other, |x, y| *x &= y) }
        }
    }
}

impl<T: Idx> From<GrowableBitSet<T>> for DenseBitSet<T> {
    fn from(bit_set: GrowableBitSet<T>) -> Self {
        bit_set.bit_set
    }
}

impl<T> Clone for DenseBitSet<T> {
    #[inline(always)]
    fn clone(&self) -> Self {
        if self.is_inline() {
            let inline = unsafe { self.inline };
            Self { inline }
        } else if self.is_empty_unallocated() {
            let empty_unallocated = unsafe { self.empty_unallocated };
            Self { empty_unallocated }
        } else {
            let old_on_heap = unsafe { &self.on_heap };
            let on_heap = old_on_heap.clone();
            Self { on_heap }
        }
    }
}

impl<T: Idx> fmt::Debug for DenseBitSet<T> {
    fn fmt(&self, w: &mut fmt::Formatter<'_>) -> fmt::Result {
        w.debug_list().entries(self.iter()).finish()
    }
}

impl<T: Idx> ToString for DenseBitSet<T> {
    fn to_string(&self) -> String {
        let mut result = String::new();
        let mut sep = '[';

        // Note: this is a little endian printout of bytes.

        // i tracks how many bits we have printed so far.
        let mut i = 0;
        for word in &self.words {
            let mut word = *word;
            for _ in 0..WORD_BYTES {
                // for each byte in `word`:
                let remain = self.domain_size - i;
                // If less than a byte remains, then mask just that many bits.
                let mask = if remain <= 8 { (1 << remain) - 1 } else { 0xFF };
                assert!(mask <= 0xFF);
                let byte = word & mask;

                result.push_str(&format!("{sep}{byte:02x}"));

                if remain <= 8 {
                    break;
                }
                word >>= 8;
                i += 8;
                sep = '-';
            }
            sep = '|';
        }
        result.push(']');

        result
    }
}

pub struct BitIter<'a, T: Idx> {
    /// A copy of the current word, but with any already-visited bits cleared.
    /// (This lets us use `trailing_zeros()` to find the next set bit.) When it
    /// is reduced to 0, we move onto the next word.
    word: Word,

    /// The offset (measured in bits) of the current word.
    offset: usize,

    /// Underlying iterator over the words.
    iter: slice::Iter<'a, Word>,

    marker: PhantomData<T>,
}

impl<'a, T: Idx> BitIter<'a, T> {
    #[inline]
    fn new(words: &'a [Word]) -> BitIter<'a, T> {
        // We initialize `word` and `offset` to degenerate values. On the first
        // call to `next()` we will fall through to getting the first word from
        // `iter`, which sets `word` to the first word (if there is one) and
        // `offset` to 0. Doing it this way saves us from having to maintain
        // additional state about whether we have started.
        BitIter {
            word: 0,
            offset: usize::MAX - (WORD_BITS - 1),
            iter: words.iter(),
            marker: PhantomData,
        }
    }
}

impl<'a, T: Idx> Iterator for BitIter<'a, T> {
    type Item = T;
    fn next(&mut self) -> Option<T> {
        loop {
            if self.word != 0 {
                // Get the position of the next set bit in the current word,
                // then clear the bit.
                let bit_pos = self.word.trailing_zeros() as usize;
                self.word ^= 1 << bit_pos;
                return Some(T::new(bit_pos + self.offset));
            }

            // Move onto the next word. `wrapping_add()` is needed to handle
            // the degenerate initial value given to `offset` in `new()`.
            self.word = *self.iter.next()?;
            self.offset = self.offset.wrapping_add(WORD_BITS);
        }
    }
}

/// A fixed-size bitset type with a partially dense, partially sparse
/// representation. The bitset is broken into chunks, and chunks that are all
/// zeros or all ones are represented and handled very efficiently.
///
/// This type is especially efficient for sets that typically have a large
/// `domain_size` with significant stretches of all zeros or all ones, and also
/// some stretches with lots of 0s and 1s mixed in a way that causes trouble
/// for `IntervalSet`.
///
/// Best used via `MixedBitSet`, rather than directly, because `MixedBitSet`
/// has better performance for small bitsets.
///
/// `T` is an index type, typically a newtyped `usize` wrapper, but it can also
/// just be `usize`.
///
/// All operations that involve an element will panic if the element is equal
/// to or greater than the domain size. All operations that involve two bitsets
/// will panic if the bitsets have differing domain sizes.
#[derive(PartialEq, Eq)]
pub struct ChunkedBitSet<T> {
    domain_size: usize,

    /// The chunks. Each one contains exactly CHUNK_BITS values, except the
    /// last one which contains 1..=CHUNK_BITS values.
    chunks: Box<[Chunk]>,

    marker: PhantomData<T>,
}

// NOTE: The chunk size is computed on-the-fly on each manipulation of a chunk.
// This avoids storing it, as it's almost always CHUNK_BITS except for the last one.
#[derive(Clone, Debug, PartialEq, Eq)]
enum Chunk {
    /// A chunk that is all zeros; we don't represent the zeros explicitly.
    Zeros,

    /// A chunk that is all ones; we don't represent the ones explicitly.
    Ones,

    /// A chunk that has a mix of zeros and ones, which are represented
    /// explicitly and densely. It never has all zeros or all ones.
    ///
    /// If this is the final chunk there may be excess, unused words. This
    /// turns out to be both simpler and have better performance than
    /// allocating the minimum number of words, largely because we avoid having
    /// to store the length, which would make this type larger. These excess
    /// words are always zero, as are any excess bits in the final in-use word.
    ///
    /// The `ChunkSize` field is the count of 1s set in the chunk, and
    /// must satisfy `0 < count < chunk_domain_size`.
    ///
    /// The words are within an `Rc` because it's surprisingly common to
    /// duplicate an entire chunk, e.g. in `ChunkedBitSet::clone_from()`, or
    /// when a `Mixed` chunk is union'd into a `Zeros` chunk. When we do need
    /// to modify a chunk we use `Rc::make_mut`.
    Mixed(ChunkSize, Rc<[Word; CHUNK_WORDS]>),
}

// This type is used a lot. Make sure it doesn't unintentionally get bigger.
#[cfg(target_pointer_width = "64")]
crate::static_assert_size!(Chunk, 16);

impl<T> ChunkedBitSet<T> {
    pub fn domain_size(&self) -> usize {
        self.domain_size
    }

    #[inline]
    fn last_chunk_size(&self) -> ChunkSize {
        let n = self.domain_size % CHUNK_BITS;
        if n == 0 { CHUNK_BITS as ChunkSize } else { n as ChunkSize }
    }

    /// All the chunks have a chunk_domain_size of `CHUNK_BITS` except the final one.
    #[inline]
    fn chunk_domain_size(&self, chunk: usize) -> ChunkSize {
        if chunk == self.chunks.len() - 1 {
            self.last_chunk_size()
        } else {
            CHUNK_BITS as ChunkSize
        }
    }

    #[cfg(test)]
    fn assert_valid(&self) {
        if self.domain_size == 0 {
            assert!(self.chunks.is_empty());
            return;
        }

        assert!((self.chunks.len() - 1) * CHUNK_BITS <= self.domain_size);
        assert!(self.chunks.len() * CHUNK_BITS >= self.domain_size);
        for (chunk_index, chunk) in self.chunks.iter().enumerate() {
            let chunk_domain_size = self.chunk_domain_size(chunk_index);
            chunk.assert_valid(chunk_domain_size);
        }
    }
}

impl<T: Idx> ChunkedBitSet<T> {
    /// Creates a new bitset with a given `domain_size` and chunk kind.
    fn new(domain_size: usize, is_empty: bool) -> Self {
        let chunks = if domain_size == 0 {
            Box::new([])
        } else {
            vec![if is_empty { Zeros } else { Ones }; num_chunks(domain_size)].into_boxed_slice()
        };
        ChunkedBitSet { domain_size, chunks, marker: PhantomData }
    }

    /// Creates a new, empty bitset with a given `domain_size`.
    #[inline]
    pub fn new_empty(domain_size: usize) -> Self {
        ChunkedBitSet::new(domain_size, /* is_empty */ true)
    }

    /// Creates a new, filled bitset with a given `domain_size`.
    #[inline]
    pub fn new_filled(domain_size: usize) -> Self {
        ChunkedBitSet::new(domain_size, /* is_empty */ false)
    }

    pub fn clear(&mut self) {
        self.chunks.fill_with(|| Chunk::Zeros);
    }

    #[cfg(test)]
    fn chunks(&self) -> &[Chunk] {
        &self.chunks
    }

    /// Count the number of bits in the set.
    pub fn count(&self) -> usize {
        self.chunks
            .iter()
            .enumerate()
            .map(|(index, chunk)| chunk.count(self.chunk_domain_size(index)))
            .sum()
    }

    pub fn is_empty(&self) -> bool {
        self.chunks.iter().all(|chunk| matches!(chunk, Zeros))
    }

    /// Returns `true` if `self` contains `elem`.
    #[inline]
    pub fn contains(&self, elem: T) -> bool {
        assert!(elem.index() < self.domain_size);
        let chunk = &self.chunks[chunk_index(elem)];
        match &chunk {
            Zeros => false,
            Ones => true,
            Mixed(_, words) => {
                let (word_index, mask) = chunk_word_index_and_mask(elem);
                (words[word_index] & mask) != 0
            }
        }
    }

    #[inline]
    pub fn iter(&self) -> ChunkedBitIter<'_, T> {
        ChunkedBitIter::new(self)
    }

    /// Insert `elem`. Returns whether the set has changed.
    pub fn insert(&mut self, elem: T) -> bool {
        assert!(elem.index() < self.domain_size);
        let chunk_index = chunk_index(elem);
        let chunk_domain_size = self.chunk_domain_size(chunk_index);
        let chunk = &mut self.chunks[chunk_index];
        match *chunk {
            Zeros => {
                if chunk_domain_size > 1 {
                    let mut words = {
                        // We take some effort to avoid copying the words.
                        let words = Rc::<[Word; CHUNK_WORDS]>::new_zeroed();
                        // SAFETY: `words` can safely be all zeroes.
                        unsafe { words.assume_init() }
                    };
                    let words_ref = Rc::get_mut(&mut words).unwrap();

                    let (word_index, mask) = chunk_word_index_and_mask(elem);
                    words_ref[word_index] |= mask;
                    *chunk = Mixed(1, words);
                } else {
                    *chunk = Ones;
                }
                true
            }
            Ones => false,
            Mixed(ref mut count, ref mut words) => {
                // We skip all the work if the bit is already set.
                let (word_index, mask) = chunk_word_index_and_mask(elem);
                if (words[word_index] & mask) == 0 {
                    *count += 1;
                    if *count < chunk_domain_size {
                        let words = Rc::make_mut(words);
                        words[word_index] |= mask;
                    } else {
                        *chunk = Ones;
                    }
                    true
                } else {
                    false
                }
            }
        }
    }

    /// Sets all bits to true.
    pub fn insert_all(&mut self) {
        self.chunks.fill_with(|| Chunk::Ones);
    }

    /// Returns `true` if the set has changed.
    pub fn remove(&mut self, elem: T) -> bool {
        assert!(elem.index() < self.domain_size);
        let chunk_index = chunk_index(elem);
        let chunk_domain_size = self.chunk_domain_size(chunk_index);
        let chunk = &mut self.chunks[chunk_index];
        match *chunk {
            Zeros => false,
            Ones => {
                if chunk_domain_size > 1 {
                    let mut words = {
                        // We take some effort to avoid copying the words.
                        let words = Rc::<[Word; CHUNK_WORDS]>::new_zeroed();
                        // SAFETY: `words` can safely be all zeroes.
                        unsafe { words.assume_init() }
                    };
                    let words_ref = Rc::get_mut(&mut words).unwrap();

                    // Set only the bits in use.
                    let num_words = num_words(chunk_domain_size as usize);
                    words_ref[..num_words].fill(!0);
                    clear_excess_bits_in_final_word(
                        chunk_domain_size as usize,
                        &mut words_ref[..num_words],
                    );
                    let (word_index, mask) = chunk_word_index_and_mask(elem);
                    words_ref[word_index] &= !mask;
                    *chunk = Mixed(chunk_domain_size - 1, words);
                } else {
                    *chunk = Zeros;
                }
                true
            }
            Mixed(ref mut count, ref mut words) => {
                // We skip all the work if the bit is already clear.
                let (word_index, mask) = chunk_word_index_and_mask(elem);
                if (words[word_index] & mask) != 0 {
                    *count -= 1;
                    if *count > 0 {
                        let words = Rc::make_mut(words);
                        words[word_index] &= !mask;
                    } else {
                        *chunk = Zeros
                    }
                    true
                } else {
                    false
                }
            }
        }
    }

    fn chunk_iter(&self, chunk_index: usize) -> ChunkIter<'_> {
        let chunk_domain_size = self.chunk_domain_size(chunk_index);
        match self.chunks.get(chunk_index) {
            Some(Zeros) => ChunkIter::Zeros,
            Some(Ones) => ChunkIter::Ones(0..chunk_domain_size as usize),
            Some(Mixed(_, words)) => {
                let num_words = num_words(chunk_domain_size as usize);
                ChunkIter::Mixed(BitIter::new(&words[0..num_words]))
            }
            None => ChunkIter::Finished,
        }
    }

    bit_relations_inherent_impls! {}
}

impl<T: Idx> BitRelations<ChunkedBitSet<T>> for ChunkedBitSet<T> {
    fn union(&mut self, other: &ChunkedBitSet<T>) -> bool {
        assert_eq!(self.domain_size, other.domain_size);

        let num_chunks = self.chunks.len();
        debug_assert_eq!(num_chunks, other.chunks.len());

        let last_chunk_size = self.last_chunk_size();
        debug_assert_eq!(last_chunk_size, other.last_chunk_size());

        let mut changed = false;
        for (chunk_index, (mut self_chunk, other_chunk)) in
            self.chunks.iter_mut().zip(other.chunks.iter()).enumerate()
        {
            let chunk_domain_size = if chunk_index + 1 == num_chunks {
                last_chunk_size
            } else {
                CHUNK_BITS as ChunkSize
            };

            match (&mut self_chunk, &other_chunk) {
                (_, Zeros) | (Ones, _) => {}
                (Zeros, _) | (Mixed(..), Ones) => {
                    // `other_chunk` fully overwrites `self_chunk`
                    *self_chunk = other_chunk.clone();
                    changed = true;
                }
                (
                    Mixed(self_chunk_count, self_chunk_words),
                    Mixed(_other_chunk_count, other_chunk_words),
                ) => {
                    // First check if the operation would change
                    // `self_chunk.words`. If not, we can avoid allocating some
                    // words, and this happens often enough that it's a
                    // performance win. Also, we only need to operate on the
                    // in-use words, hence the slicing.
                    let num_words = num_words(chunk_domain_size as usize);

                    // If both sides are the same, nothing will change. This
                    // case is very common and it's a pretty fast check, so
                    // it's a performance win to do it.
                    if self_chunk_words[0..num_words] == other_chunk_words[0..num_words] {
                        continue;
                    }

                    // Do a more precise "will anything change?" test. Also a
                    // performance win.
                    let op = |a, b| a | b;
                    if !bitwise_changes(
                        &self_chunk_words[0..num_words],
                        &other_chunk_words[0..num_words],
                        op,
                    ) {
                        continue;
                    }

                    // If we reach here, `self_chunk_words` is definitely changing.
                    let self_chunk_words = Rc::make_mut(self_chunk_words);
                    let has_changed = bitwise(
                        &mut self_chunk_words[0..num_words],
                        &other_chunk_words[0..num_words],
                        op,
                    );
                    debug_assert!(has_changed);
                    *self_chunk_count = count_ones(&self_chunk_words[0..num_words]) as ChunkSize;
                    if *self_chunk_count == chunk_domain_size {
                        *self_chunk = Ones;
                    }
                    changed = true;
                }
            }
        }
        changed
    }

    fn subtract(&mut self, other: &ChunkedBitSet<T>) -> bool {
        assert_eq!(self.domain_size, other.domain_size);

        let num_chunks = self.chunks.len();
        debug_assert_eq!(num_chunks, other.chunks.len());

        let last_chunk_size = self.last_chunk_size();
        debug_assert_eq!(last_chunk_size, other.last_chunk_size());

        let mut changed = false;
        for (chunk_index, (mut self_chunk, other_chunk)) in
            self.chunks.iter_mut().zip(other.chunks.iter()).enumerate()
        {
            let chunk_domain_size = if chunk_index + 1 == num_chunks {
                last_chunk_size
            } else {
                CHUNK_BITS as ChunkSize
            };

            match (&mut self_chunk, &other_chunk) {
                (Zeros, _) | (_, Zeros) => {}
                (Ones | Mixed(..), Ones) => {
                    changed = true;
                    *self_chunk = Zeros;
                }
                (Ones, Mixed(other_chunk_count, other_chunk_words)) => {
                    changed = true;
                    let num_words = num_words(chunk_domain_size as usize);
                    debug_assert!(num_words > 0 && num_words <= CHUNK_WORDS);
                    let mut tail_mask =
                        1 << (chunk_domain_size - ((num_words - 1) * WORD_BITS) as u16) - 1;
                    let mut self_chunk_words = **other_chunk_words;
                    for word in self_chunk_words[0..num_words].iter_mut().rev() {
                        *word = !*word & tail_mask;
                        tail_mask = Word::MAX;
                    }
                    let self_chunk_count = chunk_domain_size - *other_chunk_count;
                    debug_assert_eq!(
                        self_chunk_count,
                        count_ones(&self_chunk_words[0..num_words]) as ChunkSize
                    );
                    *self_chunk = Mixed(self_chunk_count, Rc::new(self_chunk_words));
                }
                (
                    Mixed(self_chunk_count, self_chunk_words),
                    Mixed(_other_chunk_count, other_chunk_words),
                ) => {
                    // See `ChunkedBitSet::union` for details on what is happening here.
                    let num_words = num_words(chunk_domain_size as usize);
                    let op = |a: Word, b: Word| a & !b;
                    if !bitwise_changes(
                        &self_chunk_words[0..num_words],
                        &other_chunk_words[0..num_words],
                        op,
                    ) {
                        continue;
                    }

                    let self_chunk_words = Rc::make_mut(self_chunk_words);
                    let has_changed = bitwise(
                        &mut self_chunk_words[0..num_words],
                        &other_chunk_words[0..num_words],
                        op,
                    );
                    debug_assert!(has_changed);
                    *self_chunk_count = count_ones(&self_chunk_words[0..num_words]) as ChunkSize;
                    if *self_chunk_count == 0 {
                        *self_chunk = Zeros;
                    }
                    changed = true;
                }
            }
        }
        changed
    }

    fn intersect(&mut self, other: &ChunkedBitSet<T>) -> bool {
        assert_eq!(self.domain_size, other.domain_size);

        let num_chunks = self.chunks.len();
        debug_assert_eq!(num_chunks, other.chunks.len());

        let last_chunk_size = self.last_chunk_size();
        debug_assert_eq!(last_chunk_size, other.last_chunk_size());

        let mut changed = false;
        for (chunk_index, (mut self_chunk, other_chunk)) in
            self.chunks.iter_mut().zip(other.chunks.iter()).enumerate()
        {
            let chunk_domain_size = if chunk_index + 1 == num_chunks {
                last_chunk_size
            } else {
                CHUNK_BITS as ChunkSize
            };

            match (&mut self_chunk, &other_chunk) {
                (Zeros, _) | (_, Ones) => {}
                (Ones, Zeros | Mixed(..)) | (Mixed(..), Zeros) => {
                    changed = true;
                    *self_chunk = other_chunk.clone();
                }
                (
                    Mixed(self_chunk_count, self_chunk_words),
                    Mixed(_other_chunk_count, other_chunk_words),
                ) => {
                    // See `ChunkedBitSet::union` for details on what is happening here.
                    let num_words = num_words(chunk_domain_size as usize);
                    let op = |a, b| a & b;
                    if !bitwise_changes(
                        &self_chunk_words[0..num_words],
                        &other_chunk_words[0..num_words],
                        op,
                    ) {
                        continue;
                    }

                    let self_chunk_words = Rc::make_mut(self_chunk_words);
                    let has_changed = bitwise(
                        &mut self_chunk_words[0..num_words],
                        &other_chunk_words[0..num_words],
                        op,
                    );
                    debug_assert!(has_changed);
                    *self_chunk_count = count_ones(&self_chunk_words[0..num_words]) as ChunkSize;
                    if *self_chunk_count == 0 {
                        *self_chunk = Zeros;
                    }
                    changed = true;
                }
            }
        }

        changed
    }
}

impl<T> Clone for ChunkedBitSet<T> {
    fn clone(&self) -> Self {
        ChunkedBitSet {
            domain_size: self.domain_size,
            chunks: self.chunks.clone(),
            marker: PhantomData,
        }
    }

    /// WARNING: this implementation of clone_from will panic if the two
    /// bitsets have different domain sizes. This constraint is not inherent to
    /// `clone_from`, but it works with the existing call sites and allows a
    /// faster implementation, which is important because this function is hot.
    fn clone_from(&mut self, from: &Self) {
        assert_eq!(self.domain_size, from.domain_size);
        debug_assert_eq!(self.chunks.len(), from.chunks.len());

        self.chunks.clone_from(&from.chunks)
    }
}

pub struct ChunkedBitIter<'a, T: Idx> {
    bit_set: &'a ChunkedBitSet<T>,

    // The index of the current chunk.
    chunk_index: usize,

    // The sub-iterator for the current chunk.
    chunk_iter: ChunkIter<'a>,
}

impl<'a, T: Idx> ChunkedBitIter<'a, T> {
    #[inline]
    fn new(bit_set: &'a ChunkedBitSet<T>) -> ChunkedBitIter<'a, T> {
        ChunkedBitIter { bit_set, chunk_index: 0, chunk_iter: bit_set.chunk_iter(0) }
    }
}

impl<'a, T: Idx> Iterator for ChunkedBitIter<'a, T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        loop {
            match &mut self.chunk_iter {
                ChunkIter::Zeros => {}
                ChunkIter::Ones(iter) => {
                    if let Some(next) = iter.next() {
                        return Some(T::new(next + self.chunk_index * CHUNK_BITS));
                    }
                }
                ChunkIter::Mixed(iter) => {
                    if let Some(next) = iter.next() {
                        return Some(T::new(next + self.chunk_index * CHUNK_BITS));
                    }
                }
                ChunkIter::Finished => return None,
            }
            self.chunk_index += 1;
            self.chunk_iter = self.bit_set.chunk_iter(self.chunk_index);
        }
    }
}

impl Chunk {
    #[cfg(test)]
    fn assert_valid(&self, chunk_domain_size: ChunkSize) {
        assert!(chunk_domain_size as usize <= CHUNK_BITS);
        match *self {
            Zeros | Ones => {}
            Mixed(count, ref words) => {
                assert!(0 < count && count < chunk_domain_size);

                // Check the number of set bits matches `count`.
                assert_eq!(count_ones(words.as_slice()) as ChunkSize, count);

                // Check the not-in-use words are all zeroed.
                let num_words = num_words(chunk_domain_size as usize);
                if num_words < CHUNK_WORDS {
                    assert_eq!(count_ones(&words[num_words..]) as ChunkSize, 0);
                }
            }
        }
    }

    /// Count the number of 1s in the chunk.
    fn count(&self, chunk_domain_size: ChunkSize) -> usize {
        match *self {
            Zeros => 0,
            Ones => chunk_domain_size as usize,
            Mixed(count, _) => count as usize,
        }
    }
}

enum ChunkIter<'a> {
    Zeros,
    Ones(Range<usize>),
    Mixed(BitIter<'a, usize>),
    Finished,
}

impl<T: Idx> fmt::Debug for ChunkedBitSet<T> {
    fn fmt(&self, w: &mut fmt::Formatter<'_>) -> fmt::Result {
        w.debug_list().entries(self.iter()).finish()
    }
}

/// Sets `out_vec[i] = op(out_vec[i], in_vec[i])` for each index `i` in both
/// slices. The slices must have the same length.
///
/// Returns true if at least one bit in `out_vec` was changed.
///
/// ## Warning
/// Some bitwise operations (e.g. union-not, xor) can set output bits that were
/// unset in in both inputs. If this happens in the last word/chunk of a bitset,
/// it can cause the bitset to contain out-of-domain values, which need to
/// be cleared with `clear_excess_bits_in_final_word`. This also makes the
/// "changed" return value unreliable, because the change might have only
/// affected excess bits.
#[inline]
fn bitwise<Op>(out_vec: &mut [Word], in_vec: &[Word], op: Op) -> bool
where
    Op: Fn(Word, Word) -> Word,
{
    assert_eq!(out_vec.len(), in_vec.len());
    let mut changed = 0;
    for (out_elem, in_elem) in iter::zip(out_vec, in_vec) {
        let old_val = *out_elem;
        let new_val = op(old_val, *in_elem);
        *out_elem = new_val;
        // This is essentially equivalent to a != with changed being a bool, but
        // in practice this code gets auto-vectorized by the compiler for most
        // operators. Using != here causes us to generate quite poor code as the
        // compiler tries to go back to a boolean on each loop iteration.
        changed |= old_val ^ new_val;
    }
    changed != 0
}

/// Does this bitwise operation change `out_vec`?
#[inline]
fn bitwise_changes<Op>(out_vec: &[Word], in_vec: &[Word], op: Op) -> bool
where
    Op: Fn(Word, Word) -> Word,
{
    assert_eq!(out_vec.len(), in_vec.len());
    for (out_elem, in_elem) in iter::zip(out_vec, in_vec) {
        let old_val = *out_elem;
        let new_val = op(old_val, *in_elem);
        if old_val != new_val {
            return true;
        }
    }
    false
}

/// A bitset with a mixed representation, using `DenseBitSet` for small and
/// medium bitsets, and `ChunkedBitSet` for large bitsets, i.e. those with
/// enough bits for at least two chunks. This is a good choice for many bitsets
/// that can have large domain sizes (e.g. 5000+).
///
/// `T` is an index type, typically a newtyped `usize` wrapper, but it can also
/// just be `usize`.
///
/// All operations that involve an element will panic if the element is equal
/// to or greater than the domain size. All operations that involve two bitsets
/// will panic if the bitsets have differing domain sizes.
#[derive(PartialEq, Eq)]
pub enum MixedBitSet<T> {
    Small(DenseBitSet<T>),
    Large(ChunkedBitSet<T>),
}

impl<T> MixedBitSet<T> {
    pub fn domain_size(&self) -> usize {
        match self {
            MixedBitSet::Small(set) => set.domain_size(),
            MixedBitSet::Large(set) => set.domain_size(),
        }
    }
}

impl<T: Idx> MixedBitSet<T> {
    #[inline]
    pub fn new_empty(domain_size: usize) -> MixedBitSet<T> {
        if domain_size <= CHUNK_BITS {
            MixedBitSet::Small(DenseBitSet::new_empty(domain_size))
        } else {
            MixedBitSet::Large(ChunkedBitSet::new_empty(domain_size))
        }
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        match self {
            MixedBitSet::Small(set) => set.is_empty(),
            MixedBitSet::Large(set) => set.is_empty(),
        }
    }

    #[inline]
    pub fn contains(&self, elem: T) -> bool {
        match self {
            MixedBitSet::Small(set) => set.contains(elem),
            MixedBitSet::Large(set) => set.contains(elem),
        }
    }

    #[inline]
    pub fn insert(&mut self, elem: T) -> bool {
        match self {
            MixedBitSet::Small(set) => set.insert(elem),
            MixedBitSet::Large(set) => set.insert(elem),
        }
    }

    /// Insert `0..domain_size` in the set.
    ///
    /// We would like an insert all function that doesn't require the domain size, but the exact
    /// domain size is not stored in the `Small` variant, so that is not possible.
    #[inline]
    pub fn insert_all(&mut self, domain_size: usize) {
        match self {
            MixedBitSet::Small(set) => set.insert_all(domain_size),
            MixedBitSet::Large(set) => set.insert_all(),
        }
    }

    #[inline]
    pub fn remove(&mut self, elem: T) -> bool {
        match self {
            MixedBitSet::Small(set) => set.remove(elem),
            MixedBitSet::Large(set) => set.remove(elem),
        }
    }

    pub fn iter(&self) -> MixedBitIter<'_, T> {
        match self {
            MixedBitSet::Small(set) => MixedBitIter::Small(set.iter()),
            MixedBitSet::Large(set) => MixedBitIter::Large(set.iter()),
        }
    }

    #[inline]
    pub fn clear(&mut self) {
        match self {
            MixedBitSet::Small(set) => set.clear(),
            MixedBitSet::Large(set) => set.clear(),
        }
    }

    bit_relations_inherent_impls! {}
}

impl<T> Clone for MixedBitSet<T> {
    fn clone(&self) -> Self {
        match self {
            MixedBitSet::Small(set) => MixedBitSet::Small(set.clone()),
            MixedBitSet::Large(set) => MixedBitSet::Large(set.clone()),
        }
    }

    /// WARNING: this implementation of clone_from may panic if the two
    /// bitsets have different domain sizes. This constraint is not inherent to
    /// `clone_from`, but it works with the existing call sites and allows a
    /// faster implementation, which is important because this function is hot.
    fn clone_from(&mut self, from: &Self) {
        match (self, from) {
            (MixedBitSet::Small(set), MixedBitSet::Small(from)) => set.clone_from(from),
            (MixedBitSet::Large(set), MixedBitSet::Large(from)) => set.clone_from(from),
            _ => panic!("MixedBitSet size mismatch"),
        }
    }
}

impl<T: Idx> BitRelations<MixedBitSet<T>> for MixedBitSet<T> {
    fn union(&mut self, other: &MixedBitSet<T>) -> bool {
        match (self, other) {
            (MixedBitSet::Small(set), MixedBitSet::Small(other)) => set.union(other),
            (MixedBitSet::Large(set), MixedBitSet::Large(other)) => set.union(other),
            _ => panic!("MixedBitSet size mismatch"),
        }
    }

    fn subtract(&mut self, other: &MixedBitSet<T>) -> bool {
        match (self, other) {
            (MixedBitSet::Small(set), MixedBitSet::Small(other)) => set.subtract(other),
            (MixedBitSet::Large(set), MixedBitSet::Large(other)) => set.subtract(other),
            _ => panic!("MixedBitSet size mismatch"),
        }
    }

    fn intersect(&mut self, _other: &MixedBitSet<T>) -> bool {
        unimplemented!("implement if/when necessary");
    }
}

impl<T: Idx> fmt::Debug for MixedBitSet<T> {
    fn fmt(&self, w: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MixedBitSet::Small(set) => set.fmt(w),
            MixedBitSet::Large(set) => set.fmt(w),
        }
    }
}

pub enum MixedBitIter<'a, T: Idx> {
    Small(BitIter<'a, T>),
    Large(ChunkedBitIter<'a, T>),
}

impl<'a, T: Idx> Iterator for MixedBitIter<'a, T> {
    type Item = T;
    fn next(&mut self) -> Option<T> {
        match self {
            MixedBitIter::Small(iter) => iter.next(),
            MixedBitIter::Large(iter) => iter.next(),
        }
    }
}

/// A resizable bitset type with a dense representation.
///
/// `T` is an index type, typically a newtyped `usize` wrapper, but it can also
/// just be `usize`.
///
/// All operations that involve an element will panic if the element is equal
/// to or greater than the domain size.
#[derive(Clone, Debug, PartialEq)]
pub struct GrowableBitSet<T: Idx> {
    bit_set: DenseBitSet<T>,
}

impl<T: Idx> Default for GrowableBitSet<T> {
    fn default() -> Self {
        GrowableBitSet::new_empty()
    }
}

impl<T: Idx> GrowableBitSet<T> {
    /// Ensure that the set can hold at least `min_domain_size` elements.
    pub fn ensure(&mut self, min_domain_size: usize) {
        if self.bit_set.domain_size < min_domain_size {
            self.bit_set.domain_size = min_domain_size;
        }

        let min_num_words = num_words(min_domain_size);
        if self.bit_set.words.len() < min_num_words {
            self.bit_set.words.resize(min_num_words, 0)
        }
    }

    pub fn new_empty() -> GrowableBitSet<T> {
        GrowableBitSet { bit_set: DenseBitSet::new_empty(0) }
    }

    pub fn with_capacity(capacity: usize) -> GrowableBitSet<T> {
        GrowableBitSet { bit_set: DenseBitSet::new_empty(capacity) }
    }

    /// Returns `true` if the set has changed.
    #[inline]
    pub fn insert(&mut self, elem: T) -> bool {
        self.ensure(elem.index() + 1);
        self.bit_set.insert(elem)
    }

    /// Returns `true` if the set has changed.
    #[inline]
    pub fn remove(&mut self, elem: T) -> bool {
        self.ensure(elem.index() + 1);
        self.bit_set.remove(elem)
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.bit_set.is_empty()
    }

    #[inline]
    pub fn contains(&self, elem: T) -> bool {
        let (word_index, mask) = word_index_and_mask(elem);
        self.bit_set.words.get(word_index).is_some_and(|word| (word & mask) != 0)
    }

    #[inline]
    pub fn iter(&self) -> BitIter<'_, T> {
        self.bit_set.iter()
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.bit_set.count()
    }
}

impl<T: Idx> From<DenseBitSet<T>> for GrowableBitSet<T> {
    fn from(bit_set: DenseBitSet<T>) -> Self {
        Self { bit_set }
    }
}

/// A fixed-size 2D bit matrix type with a dense representation.
///
/// `R` and `C` are index types used to identify rows and columns respectively;
/// typically newtyped `usize` wrappers, but they can also just be `usize`.
///
/// All operations that involve a row and/or column index will panic if the
/// index exceeds the relevant bound.
#[cfg_attr(feature = "nightly", derive(Decodable_NoContext, Encodable_NoContext))]
#[derive(Clone, Eq, PartialEq, Hash)]
pub struct BitMatrix<R: Idx, C: Idx> {
    num_rows: usize,
    num_columns: usize,
    words: Vec<Word>,
    marker: PhantomData<(R, C)>,
}

impl<R: Idx, C: Idx> BitMatrix<R, C> {
    /// Creates a new `rows x columns` matrix, initially empty.
    pub fn new(num_rows: usize, num_columns: usize) -> BitMatrix<R, C> {
        // For every element, we need one bit for every other
        // element. Round up to an even number of words.
        let words_per_row = num_words(num_columns);
        BitMatrix {
            num_rows,
            num_columns,
            words: vec![0; num_rows * words_per_row],
            marker: PhantomData,
        }
    }

    /// Creates a new matrix, with `row` used as the value for every row.
    pub fn from_row_n(row: &DenseBitSet<C>, num_rows: usize) -> BitMatrix<R, C> {
        let num_columns = row.domain_size();
        let words_per_row = num_words(num_columns);
        assert_eq!(words_per_row, row.words.len());
        BitMatrix {
            num_rows,
            num_columns,
            words: iter::repeat_n(&row.words, num_rows).flatten().cloned().collect(),
            marker: PhantomData,
        }
    }

    pub fn rows(&self) -> impl Iterator<Item = R> {
        (0..self.num_rows).map(R::new)
    }

    /// The range of bits for a given row.
    fn range(&self, row: R) -> (usize, usize) {
        let words_per_row = num_words(self.num_columns);
        let start = row.index() * words_per_row;
        (start, start + words_per_row)
    }

    /// Sets the cell at `(row, column)` to true. Put another way, insert
    /// `column` to the bitset for `row`.
    ///
    /// Returns `true` if this changed the matrix.
    pub fn insert(&mut self, row: R, column: C) -> bool {
        assert!(row.index() < self.num_rows && column.index() < self.num_columns);
        let (start, _) = self.range(row);
        let (word_index, mask) = word_index_and_mask(column);
        let words = &mut self.words[..];
        let word = words[start + word_index];
        let new_word = word | mask;
        words[start + word_index] = new_word;
        word != new_word
    }

    /// Do the bits from `row` contain `column`? Put another way, is
    /// the matrix cell at `(row, column)` true?  Put yet another way,
    /// if the matrix represents (transitive) reachability, can
    /// `row` reach `column`?
    pub fn contains(&self, row: R, column: C) -> bool {
        assert!(row.index() < self.num_rows && column.index() < self.num_columns);
        let (start, _) = self.range(row);
        let (word_index, mask) = word_index_and_mask(column);
        (self.words[start + word_index] & mask) != 0
    }

    /// Returns those indices that are true in rows `a` and `b`. This
    /// is an *O*(*n*) operation where *n* is the number of elements
    /// (somewhat independent from the actual size of the
    /// intersection, in particular).
    pub fn intersect_rows(&self, row1: R, row2: R) -> Vec<C> {
        assert!(row1.index() < self.num_rows && row2.index() < self.num_rows);
        let (row1_start, row1_end) = self.range(row1);
        let (row2_start, row2_end) = self.range(row2);
        let mut result = Vec::with_capacity(self.num_columns);
        for (base, (i, j)) in (row1_start..row1_end).zip(row2_start..row2_end).enumerate() {
            let mut v = self.words[i] & self.words[j];
            for bit in 0..WORD_BITS {
                if v == 0 {
                    break;
                }
                if v & 0x1 != 0 {
                    result.push(C::new(base * WORD_BITS + bit));
                }
                v >>= 1;
            }
        }
        result
    }

    /// Adds the bits from row `read` to the bits from row `write`, and
    /// returns `true` if anything changed.
    ///
    /// This is used when computing transitive reachability because if
    /// you have an edge `write -> read`, because in that case
    /// `write` can reach everything that `read` can (and
    /// potentially more).
    pub fn union_rows(&mut self, read: R, write: R) -> bool {
        assert!(read.index() < self.num_rows && write.index() < self.num_rows);
        let (read_start, read_end) = self.range(read);
        let (write_start, write_end) = self.range(write);
        let words = &mut self.words[..];
        let mut changed = 0;
        for (read_index, write_index) in iter::zip(read_start..read_end, write_start..write_end) {
            let word = words[write_index];
            let new_word = word | words[read_index];
            words[write_index] = new_word;
            // See `bitwise` for the rationale.
            changed |= word ^ new_word;
        }
        changed != 0
    }

    /// Adds the bits from `with` to the bits from row `write`, and
    /// returns `true` if anything changed.
    pub fn union_row_with(&mut self, with: &DenseBitSet<C>, write: R) -> bool {
        assert!(write.index() < self.num_rows);
        assert!(with.capacity() >= self.num_columns);
        let (write_start, write_end) = self.range(write);
        bitwise(&mut self.words[write_start..write_end], with.words().into(), |a, b| a | b)
    }

    /// Sets every cell in `row` to true.
    pub fn insert_all_into_row(&mut self, row: R) {
        assert!(row.index() < self.num_rows);
        let (start, end) = self.range(row);
        let words = &mut self.words[..];
        for index in start..end {
            words[index] = !0;
        }
        clear_excess_bits_in_final_word(self.num_columns, &mut self.words[..end]);
    }

    /// Gets a slice of the underlying words.
    pub fn words(&self) -> &[Word] {
        &self.words
    }

    /// Iterates through all the columns set to true in a given row of
    /// the matrix.
    pub fn iter(&self, row: R) -> BitIter<'_, C> {
        assert!(row.index() < self.num_rows);
        let (start, end) = self.range(row);
        BitIter::from_slice(&self.words[start..end])
    }

    /// Returns the number of elements in `row`.
    pub fn count(&self, row: R) -> usize {
        let (start, end) = self.range(row);
        count_ones(&self.words[start..end])
    }
}

impl<R: Idx, C: Idx> fmt::Debug for BitMatrix<R, C> {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        /// Forces its contents to print in regular mode instead of alternate mode.
        struct OneLinePrinter<T>(T);
        impl<T: fmt::Debug> fmt::Debug for OneLinePrinter<T> {
            fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
                write!(fmt, "{:?}", self.0)
            }
        }

        write!(fmt, "BitMatrix({}x{}) ", self.num_rows, self.num_columns)?;
        let items = self.rows().flat_map(|r| self.iter(r).map(move |c| (r, c)));
        fmt.debug_set().entries(items.map(OneLinePrinter)).finish()
    }
}

/// A fixed-column-size, variable-row-size 2D bit matrix with a moderately
/// sparse representation.
///
/// Initially, every row has no explicit representation. If any bit within a row
/// is set, the entire row is instantiated as `Some(<DenseBitSet>)`.
/// Furthermore, any previously uninstantiated rows prior to it will be
/// instantiated as `None`. Those prior rows may themselves become fully
/// instantiated later on if any of their bits are set.
///
/// `R` and `C` are index types used to identify rows and columns respectively;
/// typically newtyped `usize` wrappers, but they can also just be `usize`.
#[derive(Clone, Debug)]
pub struct SparseBitMatrix<R, C>
where
    R: Idx,
    C: Idx,
{
    num_columns: usize,
    rows: IndexVec<R, Option<DenseBitSet<C>>>,
}

impl<R: Idx, C: Idx> SparseBitMatrix<R, C> {
    /// Creates a new empty sparse bit matrix with no rows or columns.
    pub fn new(num_columns: usize) -> Self {
        Self { num_columns, rows: IndexVec::new() }
    }

    fn ensure_row(&mut self, row: R) -> &mut DenseBitSet<C> {
        // Instantiate any missing rows up to and including row `row` with an empty `DenseBitSet`.
        // Then replace row `row` with a full `DenseBitSet` if necessary.
        self.rows.get_or_insert_with(row, || DenseBitSet::new_empty(self.num_columns))
    }

    /// Sets the cell at `(row, column)` to true. Put another way, insert
    /// `column` to the bitset for `row`.
    ///
    /// Returns `true` if this changed the matrix.
    pub fn insert(&mut self, row: R, column: C) -> bool {
        self.ensure_row(row).insert(column)
    }

    /// Sets the cell at `(row, column)` to false. Put another way, delete
    /// `column` from the bitset for `row`. Has no effect if `row` does not
    /// exist.
    ///
    /// Returns `true` if this changed the matrix.
    pub fn remove(&mut self, row: R, column: C) -> bool {
        match self.rows.get_mut(row) {
            Some(Some(row)) => row.remove(column),
            _ => false,
        }
    }

    /// Sets all columns at `row` to false. Has no effect if `row` does
    /// not exist.
    pub fn clear(&mut self, row: R) {
        if let Some(Some(row)) = self.rows.get_mut(row) {
            row.clear();
        }
    }

    /// Do the bits from `row` contain `column`? Put another way, is
    /// the matrix cell at `(row, column)` true?  Put yet another way,
    /// if the matrix represents (transitive) reachability, can
    /// `row` reach `column`?
    pub fn contains(&self, row: R, column: C) -> bool {
        self.row(row).is_some_and(|r| r.contains(column))
    }

    /// Adds the bits from row `read` to the bits from row `write`, and
    /// returns `true` if anything changed.
    ///
    /// This is used when computing transitive reachability because if
    /// you have an edge `write -> read`, because in that case
    /// `write` can reach everything that `read` can (and
    /// potentially more).
    pub fn union_rows(&mut self, read: R, write: R) -> bool {
        if read == write || self.row(read).is_none() {
            return false;
        }

        self.ensure_row(write);
        if let (Some(read_row), Some(write_row)) = self.rows.pick2_mut(read, write) {
            write_row.union(read_row)
        } else {
            unreachable!()
        }
    }

    pub fn rows(&self) -> impl Iterator<Item = R> {
        self.rows.indices()
    }

    /// Iterates through all the columns set to true in a given row of
    /// the matrix.
    pub fn iter(&self, row: R) -> impl Iterator<Item = C> {
        self.row(row).into_iter().flat_map(|r| r.iter())
    }

    pub fn row(&self, row: R) -> Option<&DenseBitSet<C>> {
        self.rows.get(row)?.as_ref()
    }

    /// Intersects `row` with `set`. `set` can be either `DenseBitSet` or
    /// `ChunkedBitSet`. Has no effect if `row` does not exist.
    ///
    /// Returns true if the row was changed.
    pub fn intersect_row<Set>(&mut self, row: R, set: &Set) -> bool
    where
        DenseBitSet<C>: BitRelations<Set>,
    {
        match self.rows.get_mut(row) {
            Some(Some(row)) => row.intersect(set),
            _ => false,
        }
    }

    /// Subtracts `set` from `row`. `set` can be either `DenseBitSet` or
    /// `ChunkedBitSet`. Has no effect if `row` does not exist.
    ///
    /// Returns true if the row was changed.
    pub fn subtract_row<Set>(&mut self, row: R, set: &Set) -> bool
    where
        DenseBitSet<C>: BitRelations<Set>,
    {
        match self.rows.get_mut(row) {
            Some(Some(row)) => row.subtract(set),
            _ => false,
        }
    }

    /// Unions `row` with `set`. `set` can be either `DenseBitSet` or
    /// `ChunkedBitSet`.
    ///
    /// Returns true if the row was changed.
    pub fn union_row<Set>(&mut self, row: R, set: &Set) -> bool
    where
        DenseBitSet<C>: BitRelations<Set>,
    {
        self.ensure_row(row).union(set)
    }
}

#[inline]
fn num_words<T: Idx>(domain_size: T) -> usize {
    domain_size.index().div_ceil(WORD_BITS)
}

#[inline]
fn num_chunks<T: Idx>(domain_size: T) -> usize {
    assert!(domain_size.index() > 0);
    domain_size.index().div_ceil(CHUNK_BITS)
}

#[inline]
fn word_index_and_mask<T: Idx>(elem: T) -> (usize, Word) {
    let elem = elem.index();
    let word_index = elem / WORD_BITS;
    let mask = 1 << (elem % WORD_BITS);
    (word_index, mask)
}

#[inline]
fn chunk_index<T: Idx>(elem: T) -> usize {
    elem.index() / CHUNK_BITS
}

#[inline]
fn chunk_word_index_and_mask<T: Idx>(elem: T) -> (usize, Word) {
    let chunk_elem = elem.index() % CHUNK_BITS;
    word_index_and_mask(chunk_elem)
}

fn clear_excess_bits_in_final_word(domain_size: usize, words: &mut [Word]) {
    let num_bits_in_final_word = domain_size % WORD_BITS;
    if num_bits_in_final_word > 0 {
        let mask = (1 << num_bits_in_final_word) - 1;
        words[words.len() - 1] &= mask;
    }
}

#[inline]
fn max_bit(word: Word) -> usize {
    WORD_BITS - 1 - word.leading_zeros() as usize
}

#[inline]
fn count_ones(words: &[Word]) -> usize {
    words.iter().map(|word| word.count_ones() as usize).sum()
}

/// Integral type used to represent the bit set.
pub trait FiniteBitSetTy:
    BitAnd<Output = Self>
    + BitAndAssign
    + BitOrAssign
    + Clone
    + Copy
    + Shl
    + Not<Output = Self>
    + PartialEq
    + Sized
{
    /// Size of the domain representable by this type, e.g. 64 for `u64`.
    const DOMAIN_SIZE: u32;

    /// Value which represents the `FiniteBitSet` having every bit set.
    const FILLED: Self;
    /// Value which represents the `FiniteBitSet` having no bits set.
    const EMPTY: Self;

    /// Value for one as the integral type.
    const ONE: Self;
    /// Value for zero as the integral type.
    const ZERO: Self;

    /// Perform a checked left shift on the integral type.
    fn checked_shl(self, rhs: u32) -> Option<Self>;
    /// Perform a checked right shift on the integral type.
    fn checked_shr(self, rhs: u32) -> Option<Self>;
}

impl FiniteBitSetTy for u32 {
    const DOMAIN_SIZE: u32 = 32;

    const FILLED: Self = Self::MAX;
    const EMPTY: Self = Self::MIN;

    const ONE: Self = 1u32;
    const ZERO: Self = 0u32;

    fn checked_shl(self, rhs: u32) -> Option<Self> {
        self.checked_shl(rhs)
    }

    fn checked_shr(self, rhs: u32) -> Option<Self> {
        self.checked_shr(rhs)
    }
}

impl std::fmt::Debug for FiniteBitSet<u32> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{:032b}", self.0)
    }
}

/// A fixed-sized bitset type represented by an integer type. Indices outwith than the range
/// representable by `T` are considered set.
#[cfg_attr(feature = "nightly", derive(Decodable_NoContext, Encodable_NoContext))]
#[derive(Copy, Clone, Eq, PartialEq)]
pub struct FiniteBitSet<T: FiniteBitSetTy>(pub T);

impl<T: FiniteBitSetTy> FiniteBitSet<T> {
    /// Creates a new, empty bitset.
    pub fn new_empty() -> Self {
        Self(T::EMPTY)
    }

    /// Sets the `index`th bit.
    pub fn set(&mut self, index: u32) {
        self.0 |= T::ONE.checked_shl(index).unwrap_or(T::ZERO);
    }

    /// Unsets the `index`th bit.
    pub fn clear(&mut self, index: u32) {
        self.0 &= !T::ONE.checked_shl(index).unwrap_or(T::ZERO);
    }

    /// Sets the `i`th to `j`th bits.
    pub fn set_range(&mut self, range: Range<u32>) {
        let bits = T::FILLED
            .checked_shl(range.end - range.start)
            .unwrap_or(T::ZERO)
            .not()
            .checked_shl(range.start)
            .unwrap_or(T::ZERO);
        self.0 |= bits;
    }

    /// Is the set empty?
    pub fn is_empty(&self) -> bool {
        self.0 == T::EMPTY
    }

    /// Returns the domain size of the bitset.
    pub fn within_domain(&self, index: u32) -> bool {
        index < T::DOMAIN_SIZE
    }

    /// Returns if the `index`th bit is set.
    pub fn contains(&self, index: u32) -> Option<bool> {
        self.within_domain(index)
            .then(|| ((self.0.checked_shr(index).unwrap_or(T::ONE)) & T::ONE) == T::ONE)
    }
}

impl<T: FiniteBitSetTy> Default for FiniteBitSet<T> {
    fn default() -> Self {
        Self::new_empty()
    }
}

#[cfg(feature = "nightly")]
impl<D: Decoder, T> Decodable<D> for DenseBitSet<T> {
    #[inline(never)] // FIXME: For profiling purposes
    fn decode(d: &mut D) -> Self {
        // First we read one `Word` and check the variant.
        let word = Word::decode(d);
        if word >> WORD_BITS - 2 == 0x0 {
            // If the two most significant bits are 0, then this is the `on_heap` variant and the
            // number of words is encoded by `word`.
            let n_words = word as usize;
            assert!(
                n_words > 0,
                "DenseBitSet decoder error: At least one word must be stored with the `on_heap` variant."
            );
            let mut on_heap = BitSetOnHeap::new_empty(n_words);

            let words = on_heap.as_mut_slice();
            // All `words` are now initialised to 0x0.
            debug_assert_eq!(words.len(), n_words);

            // Decode the words one-by-one.
            for word in words.iter_mut() {
                *word = Word::decode(d);
            }

            DenseBitSet { on_heap: ManuallyDrop::new(on_heap) }
        } else {
            // Both the `inline` and `empty_unallocated` variants are encoded by one `Word`. We can
            // just assume the `inline` variant because the `empty_unallocated` variant is smaller
            // and the union is `repr(C)`.
            Self { inline: word }
        }
    }
}
