//Mathlib/Order/CompleteLattice/Defs.lean
use crate::order::{defs::partialorder::*, setnotation::*};
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
    #[allow(non_snake_case)]
    proof fn lemma_le_sSup()
        ensures
            forall|s: Set<Self>, a: Self| s.contains(a) ==> #[trigger] a.le(Self::sSup(s)),
    ;

    /// Any upper bound is more than the set supremum.
    #[allow(non_snake_case)]
    proof fn lemma_sSup_le()
        ensures
            forall|s: Set<Self>, a: Self|
                (forall|b: Self| s.contains(b) ==> b.le(a)) ==> #[trigger] Self::sSup(s).le(a),
    ;
}

} // verus!
