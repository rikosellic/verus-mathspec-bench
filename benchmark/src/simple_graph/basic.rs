use vstd::{
    prelude::*,
    relations::{irreflexive, symmetric},
};

verus! {

pub enum Sum<V, W> {
    Left(V),
    Right(W),
}

/* A simple graph is an irreflexive symmetric relation `Adj` on a vertex type `V`.
The relation describes which pairs of vertices are adjacent.
There is exactly one edge for every pair of adjacent vertices;
see `SimpleGraph.edgeSet` for the corresponding edge set.
*/

#[verifier::reject_recursive_types(V)]
pub ghost struct SimpleGraph<V> {
    pub adj: spec_fn(V, V) -> bool,
}

impl<V> SimpleGraph<V> {
    /// Constructor for simple graphs using a symmetric irreflexive boolean function.
    #[verifier::inline]
    pub open spec fn mk_simple_graph(adj: spec_fn(V, V) -> bool) -> Self
        recommends
            symmetric(adj) && irreflexive(adj),
    {
        Self { adj }
    }

    #[verifier::inline]
    pub open spec fn symmetric(self) -> bool {
        symmetric(self.adj)
    }

    #[verifier::inline]
    pub open spec fn loopless(self) -> bool {
        irreflexive(self.adj)
    }

    #[verifier::inline]
    pub open spec fn wf(self) -> bool {
        self.symmetric() && self.loopless()
    }

    pub open spec fn is_subgraph_of(self, other: Self) -> bool {
        forall|v: V, w: V| #[trigger] (self.adj)(v, w) ==> (other.adj)(v, w)
    }

    #[verifier::inline]
    pub open spec fn spec_le(self, other: Self) -> bool {
        self.is_subgraph_of(other)
    }

    /// Corresponds to Lean's `instance : Max (SimpleGraph V)` where `max x y := { Adj := x.Adj ⊔ y.Adj }`
    /// Well-formedness can be automatically inferred by Verus.
    pub open spec fn union(self, other: Self) -> Self
        recommends
            self.wf() && other.wf(),
    {
        Self::mk_simple_graph(|v, w| (self.adj)(v, w) || (other.adj)(v, w))
    }

    /// Corresponds to Lean's `instance : Min (SimpleGraph V)` where `min x y := { Adj := x.Adj ⊓ y.Adj }`
    /// Well-formedness can be automatically inferred by Verus.
    #[verifier::inline]
    pub open spec fn intersection(self, other: Self) -> Self
        recommends
            self.wf() && other.wf(),
    {
        Self::mk_simple_graph(|v, w| (self.adj)(v, w) && (other.adj)(v, w))
    }

    /// We define `Gᶜ` to be the `SimpleGraph V` such that no two adjacent vertices in `G`
    /// are adjacent in the complement, and every nonadjacent pair of vertices is adjacent
    /// (still ensuring that vertices are not adjacent to themselves). -/
    /// Corresponds to Lean's hasCompl type class for SimpleGraph
    /// Well-formedness can be automatically inferred by Verus.
    pub open spec fn compl(self) -> Self
        recommends
            self.wf(),
    {
        SimpleGraph { adj: |v, w| v != w && !(self.adj)(v, w) }
    }

    /// The difference of two graphs `x - y` has the edges of `x` with the edges of `y` removed.
    /// Corresponds to Lean's `instance sdiff : SDiff (SimpleGraph V)`
    /// Well-formedness can be automatically inferred by Verus.
    pub open spec fn sdiff(self, other: Self) -> Self
        recommends
            self.wf() && other.wf(),
    {
        SimpleGraph { adj: |v, w| (self.adj)(v, w) && !(other.adj)(v, w) }
    }

    #[verifier::inline]
    pub open spec fn spec_sub(self, other: Self) -> Self {
        self.sdiff(other)
    }

    /// Corresponds to Lean's `instance sSup : SupSet (SimpleGraph V)`
    /// Well-formedness can be automatically inferred by Verus.
    pub open spec fn sSup(s: Set<Self>) -> Self
        recommends
            s.all(|g: Self| g.wf()),
    {
        Self { adj: |a, b| s.any(|g: Self| (g.adj)(a, b)) }
    }

    /// Corresponds to Lean's `instance sInf : InfSet (SimpleGraph V)`
    /// Well-formedness can be automatically inferred by Verus.
    pub open spec fn sInf(s: Set<Self>) -> Self
        recommends
            s.all(|g: Self| g.wf()),
    {
        Self { adj: |a, b| s.all(|g: Self| (g.adj)(a, b)) && a != b }
    }
}

impl<V, W> SimpleGraph<Sum<V, W>> {
    /// Complete bipartite graph K_{|V|, |W|}
    /// Well-formedness can be automatically inferred by Verus.
    pub open spec fn complete_bipartite_graph() -> Self {
        SimpleGraph { adj: |x, y| (x is Left && y is Right) || (x is Right && y is Left) }
    }
}

} // verus!
