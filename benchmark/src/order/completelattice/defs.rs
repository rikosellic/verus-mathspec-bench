//Mathlib/Order/CompleteLattice/Defs.lean
use crate::order::{bounds::defs::*, defs::partialorder::*, setnotation::*};
use vstd::prelude::*;

/* # Definition of complete lattices

This file contains the definition of complete lattices with suprema/infima of arbitrary sets.

## Main definitions

* `sSup` and `sInf` are the supremum and the infimum of a set;
* `iSup (f : ι → α)` and `iInf (f : ι → α)` are indexed supremum and infimum of a function,
  defined as `sSup` and `sInf` of the range of this function;
* class `CompleteLattice`: a bounded lattice such that `sSup s` is always the least upper boundary
  of `s` and `sInf s` is always the greatest lower boundary of `s`;
* class `CompleteLinearOrder`: a linear ordered complete lattice.

## Naming conventions

In lemma names,
* `sSup` is called `sSup`
* `sInf` is called `sInf`
* `⨆ i, s i` is called `iSup`
* `⨅ i, s i` is called `iInf`
* `⨆ i j, s i j` is called `iSup₂`. This is an `iSup` inside an `iSup`.
* `⨅ i j, s i j` is called `iInf₂`. This is an `iInf` inside an `iInf`.
* `⨆ i ∈ s, t i` is called `biSup` for "bounded `iSup`". This is the special case of `iSup₂`
  where `j : i ∈ s`.
* `⨅ i ∈ s, t i` is called `biInf` for "bounded `iInf`". This is the special case of `iInf₂`
  where `j : i ∈ s`.

## Notation

* `⨆ i, f i` : `iSup f`, the supremum of the range of `f`;
* `⨅ i, f i` : `iInf f`, the infimum of the range of `f`. */

verus! {

/// Corresponds to Lean's `class CompleteSemilatticeSup`.
/// Note that we rarely use `CompleteSemilatticeSup`
/// (in fact, any such object is always a `CompleteLattice`, so it's usually best to start there).
///
/// Nevertheless it is sometimes a useful intermediate step in constructions.
pub trait CompleteSemilatticeSup: PartialOrder + SupSet where Self: Sized {
    /// Any element of a set is less than the set supremum.
    /// ∀ s, ∀ a ∈ s, a ≤ sSup s
    #[allow(non_snake_case)]
    proof fn lemma_le_sSup()
        ensures
            forall|s: Set<Self>| s.all(|a: Self| a.le(#[trigger] Self::sSup(s))),
    ;

    /// Any upper bound is more than the set supremum.
    /// ∀ s a, (∀ b ∈ s, b ≤ a) → sSup s ≤ a
    #[allow(non_snake_case)]
    proof fn lemma_sSup_le()
        ensures
            forall|s: Set<Self>, a: Self|
                s.all(|b: Self| b.le(a)) ==> #[trigger] Self::sSup(s).le(a),
    ;

    /// b ∈ s ==> a ≤ b ==> a ≤ sSup s
    #[allow(non_snake_case)]
    proof fn lemma_le_sSup_of_le(s: Set<Self>, a: Self, b: Self)
        requires
            s.contains(b),
            a.le(b),
        ensures
            a.le(Self::sSup(s)),
    {
        Self::lemma_le_sSup();
        Self::lemma_le_trans();

        assert(b.le(Self::sSup(s)));

        assert(a.le(Self::sSup(s)));
    }

    /// sSup s ≤ a ↔ ∀ b ∈ s, b ≤ a
    #[allow(non_snake_case)]
    proof fn lemma_sSup_le_iff(s: Set<Self>, a: Self)
        ensures
            Self::sSup(s).le(a) <==> s.all(|b: Self| b.le(a)),
    {
        Self::lemma_le_sSup();
        Self::lemma_sSup_le();
        Self::lemma_le_trans();

        if Self::sSup(s).le(a) {
            assert forall|b: Self| s.contains(b) implies b.le(a) by {
                assert(b.le(Self::sSup(s)));
                assert(b.le(a));
            };
        }
        if forall|b: Self| s.contains(b) ==> b.le(a) {
            assert(Self::sSup(s).le(a));
        }
    }

    /// a ≤ sSup s ↔ ∀ b ∈ upperBounds s, a ≤ b
    #[allow(non_snake_case)]
    proof fn lemma_le_sSup_iff(s: Set<Self>, a: Self)
        ensures
            a.le(Self::sSup(s)) <==> upperBounds(s).all(|b: Self| a.le(b)),
    {
        Self::lemma_le_sSup();
        Self::lemma_sSup_le();
        Self::lemma_le_trans();

        if a.le(Self::sSup(s)) {
            assert forall|b: Self| #[trigger] upperBounds(s).contains(b) implies a.le(b) by {
                assert(Self::sSup(s).le(b));
                assert(a.le(b));
            };
        }
        if forall|b: Self| #[trigger] upperBounds(s).contains(b) ==> a.le(b) {
            assert(upperBounds(s).contains(Self::sSup(s)));
            assert(a.le(Self::sSup(s)));
        }
    }
}

/// Corresponds to Lean's `class CompleteSemilatticeInf`.
/// Note that we rarely use `CompleteSemilatticeInf`
/// (in fact, any such object is always a `CompleteLattice`, so it's usually best to start there).
///
/// Nevertheless it is sometimes a useful intermediate step in constructions.
pub trait CompleteSemilatticeInf: PartialOrder + InfSet where Self: Sized {
    /// Any element of a set is more than the set infimum.
    /// ∀ s, ∀ a ∈ s, sInf s ≤ a
    #[allow(non_snake_case)]
    proof fn lemma_sInf_le()
        ensures
            forall|s: Set<Self>| s.all(|a: Self| (#[trigger] Self::sInf(s)).le(a)),
    ;

    /// Any lower bound is less than the set infimum.
    /// ∀ s a, (∀ b ∈ s, a ≤ b) → a ≤ sInf s
    #[allow(non_snake_case)]
    proof fn lemma_le_sInf()
        ensures
            forall|s: Set<Self>, a: Self|
                (s.all(|b: Self| a.le(b))) ==> #[trigger] a.le(Self::sInf(s)),
    ;
}

} // verus!
