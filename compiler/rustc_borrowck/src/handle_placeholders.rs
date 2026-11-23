//! Logic for lowering higher-kinded outlives constraints
//! (with placeholders and universes) and turn them into regular
//! outlives constraints.
use rustc_data_structures::frozen::Frozen;
use rustc_data_structures::fx::FxIndexMap;
use rustc_data_structures::graph::scc;
use rustc_data_structures::graph::scc::Sccs;
use rustc_index::IndexVec;
use rustc_infer::infer::RegionVariableOrigin;
use rustc_middle::mir::ConstraintCategory;
use rustc_middle::ty::{RegionVid, UniverseIndex};
use tracing::{debug, trace};

use crate::constraints::{ConstraintSccIndex, OutlivesConstraintSet};
use crate::consumers::OutlivesConstraint;
use crate::diagnostics::UniverseInfo;
use crate::region_infer::values::{LivenessValues, PlaceholderIndices};
use crate::region_infer::{ConstraintSccs, RegionDefinition, Representative, TypeTest};
use crate::ty::VarianceDiagInfo;
use crate::type_check::free_region_relations::UniversalRegionRelations;
use crate::type_check::{Locations, MirTypeckRegionConstraints};
use crate::universal_regions::UniversalRegions;
use crate::{BorrowckInferCtxt, NllRegionVariableOrigin};

/// A set of outlives constraints after rewriting to remove
/// higher-kinded constraints.
pub(crate) struct LoweredConstraints<'tcx> {
    pub(crate) constraint_sccs: Sccs<RegionVid, ConstraintSccIndex>,
    pub(crate) definitions: Frozen<IndexVec<RegionVid, RegionDefinition<'tcx>>>,
    pub(crate) scc_annotations: IndexVec<ConstraintSccIndex, RegionTracker>,
    pub(crate) outlives_constraints: Frozen<OutlivesConstraintSet<'tcx>>,
    pub(crate) type_tests: Vec<TypeTest<'tcx>>,
    pub(crate) liveness_constraints: LivenessValues,
    pub(crate) universe_causes: FxIndexMap<UniverseIndex, UniverseInfo<'tcx>>,
    pub(crate) placeholder_indices: PlaceholderIndices<'tcx>,
}

/// A Visitor for SCC annotation construction.
pub(crate) struct SccAnnotations<'d, 'tcx, A: scc::Annotation> {
    pub(crate) scc_to_annotation: IndexVec<ConstraintSccIndex, A>,
    definitions: &'d IndexVec<RegionVid, RegionDefinition<'tcx>>,
}

impl<'d, 'tcx, A: scc::Annotation> SccAnnotations<'d, 'tcx, A> {
    pub(crate) fn init(definitions: &'d IndexVec<RegionVid, RegionDefinition<'tcx>>) -> Self {
        Self { scc_to_annotation: IndexVec::new(), definitions }
    }
}

impl scc::Annotations<RegionVid> for SccAnnotations<'_, '_, RegionTracker> {
    fn new(&self, element: RegionVid) -> RegionTracker {
        RegionTracker::new(element, &self.definitions[element])
    }

    fn annotate_scc(&mut self, scc: ConstraintSccIndex, annotation: RegionTracker) {
        let idx = self.scc_to_annotation.push(annotation);
        assert!(idx == scc);
    }

    type Ann = RegionTracker;
    type SccIdx = ConstraintSccIndex;
}

#[derive(Copy, Debug, Clone, PartialEq, Eq)]
struct PlaceholderReachability {
    /// The largest-universed placeholder we can reach
    max_universe: (UniverseIndex, RegionVid),

    /// The placeholder with the smallest ID
    min_placeholder: RegionVid,

    /// The placeholder with the largest ID
    max_placeholder: RegionVid,
}

impl PlaceholderReachability {
    /// Merge the reachable placeholders of two graph components.
    fn merge(&mut self, other: &Self) {
        self.max_universe = self.max_universe.max(other.max_universe);
        self.min_placeholder = self.min_placeholder.min(other.min_placeholder);
        self.max_placeholder = self.max_placeholder.max(other.max_placeholder);
    }
}

/// An annotation for region graph SCCs that tracks
/// the values of its elements. This annotates a single SCC.
#[derive(Copy, Debug, Clone)]
pub(crate) struct RegionTracker {
    reachable_placeholders: Option<PlaceholderReachability>,

    /// The largest universe nameable from this SCC.
    /// It is the smallest nameable universes of all
    /// existential regions reachable from it. Small Rvids are preferred.
    max_nameable_universe: (UniverseIndex, RegionVid),

    /// The representative Region Variable Id for this SCC.
    pub(crate) representative: Representative,
}

impl RegionTracker {
    pub(crate) fn new(rvid: RegionVid, definition: &RegionDefinition<'_>) -> Self {
        let reachable_placeholders =
            if matches!(definition.origin, NllRegionVariableOrigin::Placeholder(_)) {
                Some(PlaceholderReachability {
                    max_universe: (definition.universe, rvid),
                    min_placeholder: rvid,
                    max_placeholder: rvid,
                })
            } else {
                None
            };

        Self {
            reachable_placeholders,
            max_nameable_universe: (definition.universe, rvid),
            representative: Representative::new(rvid, definition),
        }
    }

    /// The largest universe this SCC can name. It's the smallest
    /// max-nameable-universe of any reachable region, or
    /// `max_nameable(r) = min (max_nameable(r') for r' reachable from r)`
    pub(crate) fn max_nameable_universe(self) -> UniverseIndex {
        self.max_nameable_universe.0
    }

    /// Same as `max_nameable_universe()` but also return the most restrictive existential that got us there.
    pub(crate) fn max_nameable_univere_and_existential(self) -> (UniverseIndex, RegionVid) {
        self.max_nameable_universe
    }

    pub(crate) fn max_placeholder_universe_reached(self) -> UniverseIndex {
        self.reachable_placeholders.map(|pls| pls.max_universe.0).unwrap_or(UniverseIndex::ROOT)
    }

    /// Can all reachable placeholders be named from `from`?
    /// True vacuously in case no placeholders were reached.
    fn placeholders_can_be_named_by(&self, from: UniverseIndex) -> bool {
        self.reachable_placeholders.is_none_or(|pls| from.can_name(pls.max_universe.0))
    }

    /// Determine if we can name all the placeholders in `other`.
    pub(crate) fn can_name_all_placeholders(&self, other: Self) -> bool {
        // HACK: We first check whether we can name the highest existential universe
        // of `other`. This only exists to avoid errors in case that scc already
        // depends on a placeholder it cannot name itself.
        self.max_nameable_universe().can_name(other.max_nameable_universe())
            || other.placeholders_can_be_named_by(self.max_nameable_universe.0)
    }

    /// If this SCC reaches a placeholder it can't name, return it.
    fn unnameable_placeholder(&self) -> Option<(UniverseIndex, RegionVid)> {
        self.reachable_placeholders
            .filter(|pls| !self.max_nameable_universe().can_name(pls.max_universe.0))
            .map(|pls| pls.max_universe)
    }
}

impl scc::Annotation for RegionTracker {
    fn update_scc(&mut self, other: &Self) {
        trace!("{:?} << {:?}", self.representative, other.representative);
        self.representative = self.representative.min(other.representative);
        self.update_reachable(other);
    }

    fn update_reachable(&mut self, other: &Self) {
        self.max_nameable_universe = self.max_nameable_universe.min(other.max_nameable_universe);
        match (self.reachable_placeholders.as_mut(), other.reachable_placeholders.as_ref()) {
            (None, None) | (Some(_), None) => (),
            (None, Some(theirs)) => self.reachable_placeholders = Some(*theirs),
            (Some(ours), Some(theirs)) => ours.merge(theirs),
        };
    }
}

/// Determines if the region variable definitions contain
/// placeholders, and compute them for later use.
// FIXME: This is also used by opaque type handling. Move it to a separate file.
pub(super) fn region_definitions<'tcx>(
    infcx: &BorrowckInferCtxt<'tcx>,
    universal_regions: &UniversalRegions<'tcx>,
) -> (Frozen<IndexVec<RegionVid, RegionDefinition<'tcx>>>, bool) {
    let var_infos = infcx.get_region_var_infos();
    // Create a RegionDefinition for each inference variable. This happens here because
    // it allows us to sneak in a cheap check for placeholders. Otherwise, its proper home
    // is in `RegionInferenceContext::new()`, probably.
    let mut definitions = IndexVec::with_capacity(var_infos.len());
    let mut has_placeholders = false;

    for info in var_infos.iter() {
        let origin = match info.origin {
            RegionVariableOrigin::Nll(origin) => origin,
            _ => NllRegionVariableOrigin::Existential { name: None },
        };

        let definition = RegionDefinition { origin, universe: info.universe, external_name: None };

        has_placeholders |= matches!(origin, NllRegionVariableOrigin::Placeholder(_));
        definitions.push(definition);
    }

    // Add external names from universal regions in fun function definitions.
    // FIXME: this two-step method is annoying, but I don't know how to avoid it.
    for (external_name, variable) in universal_regions.named_universal_regions_iter() {
        debug!("region {:?} has external name {:?}", variable, external_name);
        definitions[variable].external_name = Some(external_name);
    }
    (Frozen::freeze(definitions), has_placeholders)
}

/// This method handles placeholders by rewriting the constraint
/// graph. For each strongly connected component in the constraint
/// graph such that there is a series of constraints
///    A: B: C: ... : X  where
/// A contains a placeholder whose universe cannot be named by X,
/// add a constraint that X: 'static. This is a safe upper bound
/// in the face of borrow checker/trait solver limitations that will
/// eventually go away.
///
/// For a more precise definition, see the documentation for
/// [`RegionTracker`] and its methods!
///
/// This edge case used to be handled during constraint propagation.
/// It was rewritten as part of the Polonius project with the goal of moving
/// higher-kindedness concerns out of the path of the borrow checker,
/// for two reasons:
///
/// 1. Implementing Polonius is difficult enough without also
///     handling them.
/// 2. The long-term goal is to handle higher-kinded concerns
///     in the trait solver, where they belong. This avoids
///     logic duplication and allows future trait solvers
///     to compute better bounds than for example our
///     "must outlive 'static" here.
///
/// This code is a stop-gap measure in preparation for the future trait solver.
///
/// Every constraint added by this method is an internal `IllegalUniverse` constraint.
pub(crate) fn compute_sccs_applying_placeholder_outlives_constraints<'tcx>(
    constraints: MirTypeckRegionConstraints<'tcx>,
    universal_region_relations: &Frozen<UniversalRegionRelations<'tcx>>,
    infcx: &BorrowckInferCtxt<'tcx>,
) -> LoweredConstraints<'tcx> {
    let universal_regions = &universal_region_relations.universal_regions;
    let (definitions, has_placeholders) = region_definitions(infcx, universal_regions);

    let MirTypeckRegionConstraints {
        placeholder_indices,
        placeholder_index_to_region: _,
        liveness_constraints,
        mut outlives_constraints,
        universe_causes,
        type_tests,
    } = constraints;

    let fr_static = universal_regions.fr_static;
    let compute_sccs =
        |constraints: &OutlivesConstraintSet<'tcx>,
         annotations: &mut SccAnnotations<'_, 'tcx, RegionTracker>| {
            ConstraintSccs::new_with_annotation(
                &constraints.graph(definitions.len()).region_graph(constraints, fr_static),
                annotations,
            )
        };

    let mut scc_annotations = SccAnnotations::init(&definitions);
    let constraint_sccs = compute_sccs(&outlives_constraints, &mut scc_annotations);

    // This code structure is a bit convoluted because it allows for a planned
    // future change where the early return here has a different type of annotation
    // that does much less work.
    if !has_placeholders {
        debug!("No placeholder regions found; skipping rewriting logic!");

        return LoweredConstraints {
            type_tests,
            constraint_sccs,
            scc_annotations: scc_annotations.scc_to_annotation,
            definitions,
            outlives_constraints: Frozen::freeze(outlives_constraints),
            liveness_constraints,
            universe_causes,
            placeholder_indices,
        };
    }
    debug!("Placeholders present; activating placeholder handling logic!");

    let added_constraints = rewrite_placeholder_outlives(
        &constraint_sccs,
        &scc_annotations,
        fr_static,
        &mut outlives_constraints,
    );

    if added_constraints {
        eprintln!("ADDED CONSTRAINTS!");
    }

    let (constraint_sccs, scc_annotations) = if added_constraints {
        let mut annotations = SccAnnotations::init(&definitions);

        // We changed the constraint set and so must recompute SCCs.
        // Optimisation opportunity: if we can add them incrementally (and that's
        // possible because edges to 'static always only merge SCCs into 'static),
        // we would potentially save a lot of work here.
        (compute_sccs(&outlives_constraints, &mut annotations), annotations.scc_to_annotation)
    } else {
        // If we didn't add any back-edges; no more work needs doing
        debug!("No constraints rewritten!");
        (constraint_sccs, scc_annotations.scc_to_annotation)
    };

    LoweredConstraints {
        constraint_sccs,
        definitions,
        scc_annotations,
        outlives_constraints: Frozen::freeze(outlives_constraints),
        type_tests,
        liveness_constraints,
        universe_causes,
        placeholder_indices,
    }
}

pub(crate) fn rewrite_placeholder_outlives<'tcx>(
    sccs: &Sccs<RegionVid, ConstraintSccIndex>,
    annotations: &SccAnnotations<'_, '_, RegionTracker>,
    fr_static: RegionVid,
    outlives_constraints: &mut OutlivesConstraintSet<'tcx>,
) -> bool {
    // Changed to `true` if we added any constraints and need to
    // recompute SCCs.
    let mut added_constraints = false;

    let definitions = annotations.definitions;
    let annotations = &annotations.scc_to_annotation;

    for scc in sccs.all_sccs() {
        // No point in adding 'static: 'static!
        if scc == sccs.scc(fr_static) {
            continue;
        }

        let annotation = annotations[scc];
        debug!(?annotation);

        // Placeholder regions have two special error conditions, both of which are
        // handled later, in `RegionInference::check_bound_region()`.
        if let Representative::Placeholder(p) = annotation.representative {
            // Case 1: placeholder outlives another placeholder: requires no special treatment.

            // Case 2: we are a placeholder for a bound region that outlived an existential
            // that cannot name us. This will appear as `U(SCC('p)) < U('p)`, i.e. the placeholder
            // is no longer nameable by its own SCC.
            if annotation.max_nameable_universe().cannot_name(definitions[p].universe) {
                debug!(
                    "Placeholder {p:?} ({scc:?}) outlives existential that cannot name it {:?}!",
                    annotation.max_nameable_univere_and_existential()
                );
                // No use forcing `'p: 'static`; that will only ever generate extra errors
                continue;
            }
        }

        let Some((max_u, max_u_rvid)) = annotation.unnameable_placeholder() else {
            continue;
        };

        debug!(
            "Placeholder universe {max_u:?} is too large for its SCC, represented by {:?}",
            annotation.representative
        );

        // We only add one `r: 'static` constraint per SCC, where `r` is the SCC representative.
        // That constraint is annotated with some placeholder `unnameable` where
        // `unnameable` is unnameable from `r` and there is a path in the constraint graph
        // between them.

        let blame_to = max_u_rvid;
        assert!(
            matches!(definitions[blame_to].origin, NllRegionVariableOrigin::Placeholder(_)),
            "{blame_to:?} should have been a placeholder!"
        );
        assert!(
            max_u_rvid != annotation.representative.rvid(),
            "Would have added a cyclic constraint to/from {max_u_rvid:?}. This should never happen!"
        );

        // FIXME: if we can extract a useful blame span here, future error
        // reporting and constraint search can be simplified.

        added_constraints = true;
        outlives_constraints.push(OutlivesConstraint {
            sup: annotation.representative.rvid(),
            sub: fr_static,
            category: ConstraintCategory::OutlivesUnnameablePlaceholder(blame_to),
            locations: Locations::All(rustc_span::DUMMY_SP),
            span: rustc_span::DUMMY_SP,
            variance_info: VarianceDiagInfo::None,
            from_closure: false,
        });
    }
    added_constraints
}
