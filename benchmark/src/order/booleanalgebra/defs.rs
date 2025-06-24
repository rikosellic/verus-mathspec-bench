/*
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Bryan Gin-ge Chen
*/
// Mathlib/Order/BooleanAlgebra/Defs.lean
// Translated to Verus by: Xinyi Wan, 2025.
use crate::order::{lattice::*, notation::*};
use vstd::prelude::*;

/*
# (Generalized) Boolean algebras

This file sets up the theory of (generalized) Boolean algebras.

A Boolean algebra is a bounded distributive lattice with a complement operator. Boolean algebras
generalize the (classical) logic of propositions and the lattice of subsets of a set.

Generalized Boolean algebras may be less familiar, but they are essentially Boolean algebras which
do not necessarily have a top element (`⊤`) (and hence not all elements may have complements). One
example in mathlib is `Finset α`, the type of all finite subsets of an arbitrary
(not-necessarily-finite) type `α`.

`GeneralizedBooleanAlgebra α` is defined to be a distributive lattice with bottom (`⊥`) admitting
a *relative* complement operator, written using "set difference" notation as `x \ y` (`sdiff x y`).
For convenience, the `BooleanAlgebra` type class is defined to extend `GeneralizedBooleanAlgebra`
so that it is also bundled with a `\` operator.

(A terminological point: `x \ y` is the complement of `y` relative to the interval `[⊥, x]`. We do
not yet have relative complements for arbitrary intervals, as we do not even have lattice
intervals.)

## Main declarations

* `GeneralizedBooleanAlgebra`: a type class for generalized Boolean algebras
* `BooleanAlgebra`: a type class for Boolean algebras.
* `Prop.booleanAlgebra`: the Boolean algebra instance on `Prop`

## Implementation notes

The `sup_inf_sdiff` and `inf_inf_sdiff` axioms for the relative complement operator in
`GeneralizedBooleanAlgebra` are taken from
[Wikipedia](https://en.wikipedia.org/wiki/Boolean_algebra_(structure)#Generalizations).

[Stone's paper introducing generalized Boolean algebras][Stone1935] does not define a relative
complement operator `a \ b` for all `a`, `b`. Instead, the postulates there amount to an assumption
that for all `a, b : α` where `a ≤ b`, the equations `x ⊔ a = b` and `x ⊓ a = ⊥` have a solution
`x`. `Disjoint.sdiff_unique` proves that this `x` is in fact `b \ a`.

## References

* <https://en.wikipedia.org/wiki/Boolean_algebra_(structure)#Generalizations>
* [*Postulates for Boolean Algebras and Generalized Boolean Algebras*, M.H. Stone][Stone1935]
* [*Lattice Theory: Foundation*, George Grätzer][Gratzer2011]

## Tags

generalized Boolean algebras, Boolean algebras, lattices, sdiff, compl

*/

verus! {

/// Corresponds to Lean's `class GeneralizedBooleanAlgebra`.
/// A generalized Boolean algebra is a distributive lattice with `⊥` and a relative complement
/// operation `\` (called `sdiff`, after "set difference") satisfying `(a ⊓ b) ⊔ (a \ b) = a` and
/// `(a ⊓ b) ⊓ (a \ b) = ⊥`, i.e. `a \ b` is the complement of `b` in `a`.
///
/// This is a generalization of Boolean algebras which applies to `Finset α` for arbitrary
/// (not-necessarily-`Fintype`) `α`.
pub trait GeneralizedBooleanAlgebra: DistribLattice + SDiff + Bot where Self: Sized {
    /// For any `a`, `b`, `(a ⊓ b) ⊔ (a \ b) = a`
    proof fn lemma_sup_inf_sdiff()
        ensures
            forall|a: Self, b: Self| #[trigger] a.inf(b).sup(a.sdiff(b)) == a,
    ;

    /// For any `a`, `b`, `(a ⊓ b) ⊓ (a \ b) = ⊥`
    proof fn lemma_inf_inf_sdiff()
        ensures
            forall|a: Self, b: Self| #[trigger] a.inf(b).inf(a.sdiff(b)) == Self::bot(),
    ;
}

} // verus!
