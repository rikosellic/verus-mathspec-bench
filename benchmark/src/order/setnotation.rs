//mathlib4/Mathlib/Order/SetNotation.lean
use vstd::prelude::*;

verus! {

/// Corresponds to Lean's `class SupSet (α : Type*)`
pub trait SupSet where Self: Sized {
    /// Supremum of a set
    #[allow(non_snake_case)]
    spec fn sSup(s: Set<Self>) -> Self;
}

/// Corresponds to Lean's `class InfSet (α : Type*)`
/// Class for the `sInf` operator
pub trait InfSet where Self: Sized {
    /// Infimum of a set
    #[allow(non_snake_case)]
    spec fn sInf(s: Set<Self>) -> Self;
}

} // verus!
