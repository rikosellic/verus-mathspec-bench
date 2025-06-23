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

pub open spec fn range<I, T>(f: spec_fn(I) -> T) -> Set<T> {
    Set::new(|x: T| exists|y: I| #[trigger] f(y) == x)
}

/// Indexed supremum
#[allow(non_snake_case)]
pub open spec fn iSup<I, T: SupSet>(s: spec_fn(I) -> T) -> T {
    T::sSup(range(s))
}

/// Indexed infimum
#[allow(non_snake_case)]
pub open spec fn iInf<I, T: InfSet>(s: spec_fn(I) -> T) -> T {
    T::sInf(range(s))
}

} // verus!
