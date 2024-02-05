#![deny(rustc::untranslatable_diagnostic)]
#![deny(rustc::diagnostic_outside_of_impl)]

use itertools::Itertools;
use rustc_data_structures::graph::scc::Sccs;
use rustc_index::{IndexSlice, IndexVec};
use rustc_infer::infer::NllRegionVariableOrigin;
use rustc_middle::mir::ConstraintCategory;
use rustc_middle::ty::{Placeholder, RegionVid, VarianceDiagInfo};
use rustc_span::Span;
use std::fmt;
use std::ops::Index;

use crate::region_infer::RegionDefinition;
use crate::type_check::Locations;
use crate::universal_regions::UniversalRegions;

pub(crate) mod graph;

/// A set of NLL region constraints. These include "outlives"
/// constraints of the form `R1: R2`. Each constraint is identified by
/// a unique `OutlivesConstraintIndex` and you can index into the set
/// (`constraint_set[i]`) to access the constraint details.
#[derive(Clone, Debug, Default)]
pub(crate) struct OutlivesConstraintSet<'tcx> {
    outlives: IndexVec<OutlivesConstraintIndex, OutlivesConstraint<'tcx>>,
}

impl<'tcx> OutlivesConstraintSet<'tcx> {
    pub(crate) fn push(&mut self, constraint: OutlivesConstraint<'tcx>) {
        debug!("OutlivesConstraintSet::push({:?})", constraint);
        if constraint.sup == constraint.sub {
            // 'a: 'a is pretty uninteresting
            return;
        }
        self.outlives.push(constraint);
    }

    /// Constructs a "normal" graph from the constraint set; the graph makes it
    /// easy to find the constraints affecting a particular region.
    ///
    /// N.B., this graph contains a "frozen" view of the current
    /// constraints. Any new constraints added to the `OutlivesConstraintSet`
    /// after the graph is built will not be present in the graph.
    pub(crate) fn graph(&self, num_region_vars: usize) -> graph::NormalConstraintGraph {
        graph::ConstraintGraph::new(graph::Normal, self, num_region_vars)
    }

    /// Like `graph`, but constraints a reverse graph where `R1: R2`
    /// represents an edge `R2 -> R1`.
    pub(crate) fn reverse_graph(&self, num_region_vars: usize) -> graph::ReverseConstraintGraph {
        graph::ConstraintGraph::new(graph::Reverse, self, num_region_vars)
    }

    /// Computes cycles (SCCs) in the graph of regions. In particular,
    /// find all regions R1, R2 such that R1: R2 and R2: R1 and group
    /// them into an SCC, and find the relationships between SCCs.
    pub(crate) fn compute_sccs(
        &self,
        constraint_graph: &graph::NormalConstraintGraph,
        static_region: RegionVid,
    ) -> Sccs<RegionVid, ConstraintSccIndex> {
        let region_graph = &constraint_graph.region_graph(self, static_region);
        Sccs::new(region_graph)
    }

    pub(crate) fn outlives(
        &self,
    ) -> &IndexSlice<OutlivesConstraintIndex, OutlivesConstraint<'tcx>> {
        &self.outlives
    }

    /// Produces a new constraint set where placeholders outlive 'static.
    pub(crate) fn placeholders_to_static(
        &self,
        universal_regions: &UniversalRegions<'tcx>,
        definitions: &IndexVec<RegionVid, RegionDefinition<'tcx>>,
    ) -> Self {
        use NllRegionVariableOrigin as RVO;

        let mut copy = self.clone();
        let universes_incompatible = |rvid: RegionVid, placeholder: Placeholder<_>| {
            !definitions[rvid].universe.can_name(placeholder.universe) // THINK: is this sufficient given a non-scc universe?
        };

        let outlives_static = |rvid: RegionVid| OutlivesConstraint {
            sup: rvid,
            sub: universal_regions.fr_static, // All the following values are made up ex nihil
            category: ConstraintCategory::Internal,
            locations: Locations::All(rustc_span::DUMMY_SP),
            span: rustc_span::DUMMY_SP,
            variance_info: VarianceDiagInfo::None,
            from_closure: false,
        };

        let should_be_static = definitions
            .indices()
            .filter_map(|rvid| match definitions[rvid].origin {
                RVO::FreeRegion => Some(rvid), // Free regions must outlive the context: replace with 'static.
                // Incompatible universes are only ok if they overlap in the runtime of the program, i.e. 'static.
                RVO::Placeholder(p) if universes_incompatible(rvid, p) => Some(rvid),
                // Nothing to do for the other cases:
                RVO::Placeholder(_) => None, // The universes are compatible, so this is a regular subset membership
                RVO::Existential { .. } => None, // Existentially quantified region variables are fine, WHY EXACTLY?
            })
            .sorted()
            .dedup();

        for rvid in should_be_static {
            println!("New code: having {:?} ({:?}) outlive 'static", rvid, definitions[rvid]);
            copy.push(outlives_static(rvid));
        }

        copy
    }
}

impl<'tcx> Index<OutlivesConstraintIndex> for OutlivesConstraintSet<'tcx> {
    type Output = OutlivesConstraint<'tcx>;

    fn index(&self, i: OutlivesConstraintIndex) -> &Self::Output {
        &self.outlives[i]
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
pub struct OutlivesConstraint<'tcx> {
    // NB. The ordering here is not significant for correctness, but
    // it is for convenience. Before we dump the constraints in the
    // debugging logs, we sort them, and we'd like the "super region"
    // to be first, etc. (In particular, span should remain last.)
    /// The region SUP must outlive SUB...
    pub sup: RegionVid,

    /// Region that must be outlived.
    pub sub: RegionVid,

    /// Where did this constraint arise?
    pub locations: Locations,

    /// The `Span` associated with the creation of this constraint.
    /// This should be used in preference to obtaining the span from
    /// `locations`, since the `locations` may give a poor span
    /// in some cases (e.g. converting a constraint from a promoted).
    pub span: Span,

    /// What caused this constraint?
    pub category: ConstraintCategory<'tcx>,

    /// Variance diagnostic information
    pub variance_info: VarianceDiagInfo<'tcx>,

    /// If this constraint is promoted from closure requirements.
    pub from_closure: bool,
}

impl<'tcx> fmt::Debug for OutlivesConstraint<'tcx> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "({:?}: {:?}) due to {:?} ({:?}) ({:?})",
            self.sup, self.sub, self.locations, self.variance_info, self.category,
        )
    }
}

rustc_index::newtype_index! {
    #[debug_format = "OutlivesConstraintIndex({})"]
    pub struct OutlivesConstraintIndex {}
}

rustc_index::newtype_index! {
    #[orderable]
    #[debug_format = "ConstraintSccIndex({})"]
    pub struct ConstraintSccIndex {}
}
