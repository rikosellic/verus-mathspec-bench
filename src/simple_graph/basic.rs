use vstd::{prelude::*, relations::{irreflexive, symmetric}};

verus!{

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
    pub open spec fn symmetric(self) -> bool {
        symmetric(self.adj)
    }

    pub open spec fn loopless(self) -> bool {
        irreflexive(self.adj)
    }

    pub open spec fn wf(self) -> bool {
        self.symmetric() && self.loopless()
    }

    pub proof fn irrefl(self, v: V)
        requires self.wf()
        ensures !(self.adj)(v, v)
    {}

    pub proof fn adj_symm(self, x: V, y: V)
        requires self.wf() && (self.adj)(x, y)
        ensures (self.adj)(y, x)
    {}

    pub proof fn ne_of_adj(self, x: V, y: V)
        requires self.wf() && (self.adj)(x, y)
        ensures x != y
    {}

    pub proof fn ne_of_adj_of_not_adj(self, v: V, w: V, x: V)
        requires self.wf() && (self.adj)(v, x) && !(self.adj)(w, x)
        ensures v != w
    {}
}

/// Constructor for simple graphs using a symmetric irreflexive boolean function.
pub open spec fn mk_simple_graph<V>(
    adj: spec_fn(V, V) -> bool,
) -> SimpleGraph<V>
    recommends symmetric(adj) && irreflexive(adj)
{
    SimpleGraph { adj }
}

pub enum Sum<V, W> {
    Left(V),
    Right(W),
}


/// Complete bipartite graph K_{|V|, |W|}
pub open spec fn complete_bipartite_graph<V, W>() -> SimpleGraph<Sum<V, W>> {
    SimpleGraph {
        adj: |x, y| (x is Left && y is Right) || (x is Right && y is Left),
    }
}

pub proof fn complete_bipartite_graph_wf<V, W>()
    ensures complete_bipartite_graph::<V, W>().wf()
{}

}