//mathlib4/Mathlib/Order/Lattice.lean
/*
Semilattices are partially ordered sets with join (least upper bound, or `sup`) or meet (greatest
lower bound, or `inf`) operations. Lattices are posets that are both join-semilattices and
meet-semilattices.

Distributive lattices are lattices which satisfy any of four equivalent distributivity properties,
of `sup` over `inf`, on the left or on the right.
*/
use crate::order::defs::partialorder::*;
use vstd::prelude::*;

verus! {

/// Corresponds to Lean's `class SemilatticeSup (α : Type*) extends PartialOrder α`.
/// A `SemilatticeSup` is a join-semilattice, that is, a partial order
/// with a join (a.k.a. lub / least upper bound, sup / supremum) operation
/// `⊔` which is the least element larger than both factors. -/
pub trait SemilatticeSup: PartialOrder where Self: Sized {
    /// The binary supremum, used to derive `Max α`
    spec fn sup(self, rhs: Self) -> Self;

    /// The supremum is an upper bound on the first argument
    proof fn lemma_le_sup_left()
        ensures
            forall|a: Self, b: Self| #[trigger] a.le(a.sup(b)),
    ;

    /// The supremum is an upper bound on the second argument
    proof fn lemma_le_sup_right()
        ensures
            forall|a: Self, b: Self| #[trigger] b.le(a.sup(b)),
    ;

    /// The supremum is the *least* upper bound
    proof fn lemma_sup_le()
        ensures
            forall|a: Self, b: Self, c: Self| a.le(c) && b.le(c) ==> #[trigger] a.sup(b).le(c),
    ;

    // Derived lemmas
    proof fn lemma_le_sup_of_le_left(a: Self, b: Self, c: Self)
        requires
            c.le(a),
        ensures
            c.le(a.sup(b)),
    {
        assert(a.le(a.sup(b))) by { Self::lemma_le_sup_left() };
        assert(c.le(a) ==> a.le(a.sup(b)) ==> c.le(a.sup(b))) by {
            Self::lemma_le_trans();
        };
    }

    proof fn lemma_le_sup_of_le_right(a: Self, b: Self, c: Self)
        requires
            c.le(b),
        ensures
            c.le(a.sup(b)),
    {
        assert(b.le(a.sup(b))) by {
            Self::lemma_le_sup_right();
        };
        assert(c.le(b) ==> b.le(a.sup(b)) ==> c.le(a.sup(b))) by {
            Self::lemma_le_trans();
        };
    }
}

impl<T: SemilatticeSup> Max for T {
    open spec fn max(self, rhs: Self) -> Self {
        self.sup(rhs)
    }
}

} // verus!
