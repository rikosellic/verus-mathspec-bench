// SPDX-License-Identifier: Apache-2.0
//
// Copyright (c) 2017 Johannes Hölzl. All rights reserved.
// Released under the Apache License, Version 2.0 as described in the file LICENSE.
// Authors: Johannes Hölzl, Patrick Massot, Yury Kudryashov
//
// Copyright (c) 2025 Xinyi Wan. All rights reserved.
//
// This file is a Verus transcription of mathlib4/Mathlib/Order/SetNotation.lean originally written in Lean 4,
// with adaptations and modifications by Xinyi Wan (2025).
// Source: https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Order/SetNotation.lean
use vstd::prelude::*;

verus! {

/// Corresponds to Lean's `class SupSet (α : Type*)`
pub trait SupSet where Self: Sized {
    /// Supremum of a set
    spec fn sSup(s: Set<Self>) -> Self;
}

/// Corresponds to Lean's `class InfSet (α : Type*)`
/// Class for the `sInf` operator
pub trait InfSet where Self: Sized {
    /// Infimum of a set
    spec fn sInf(s: Set<Self>) -> Self;
}

pub open spec fn range<I, T>(f: spec_fn(I) -> T) -> Set<T> {
    Set::new(|x: T| exists|y: I| #[trigger] f(y) == x)
}

/// Indexed supremum
pub open spec fn iSup<I, T: SupSet>(s: spec_fn(I) -> T) -> T {
    T::sSup(range(s))
}

/// Indexed infimum
pub open spec fn iInf<I, T: InfSet>(s: spec_fn(I) -> T) -> T {
    T::sInf(range(s))
}

} // verus!
