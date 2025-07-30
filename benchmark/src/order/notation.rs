// SPDX-License-Identifier: Apache-2.0
//
// Copyright (c) 2017 Johannes Hölzl. All rights reserved.
// Released under the Apache License, Version 2.0 as described in the file LICENSE.
// Authors: Johannes Hölzl, Yury Kudryashov, Yaël Dillies
//
// Copyright (c) 2025 Xinyi Wan. All rights reserved.
//
// This file is a Verus transcription of Mathlib/Order/Notation.lean originally written in Lean 4,
// with adaptations and modifications by Xinyi Wan (2025).
// Source: https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Order/Notation.lean
use vstd::prelude::*;

/*  # Notation classes for lattice operations

 In this file we introduce typeclasses and definitions for lattice operations.

 ## Main definitions

 * `HasCompl`: type class for the `ᶜ` notation
 * `Top`: type class for the `⊤` notation
 * `Bot`: type class for the `⊥` notation

 ## Notations

 * `xᶜ`: complement in a lattice;
 * `x ⊔ y`: supremum/join, which is notation for `max x y`;
 * `x ⊓ y`: infimum/meet, which is notation for `min x y`;

 We implement a delaborator that pretty prints `max x y`/`min x y` as `x ⊔ y`/`x ⊓ y`
 if and only if the order on `α` does not have a `LinearOrder α` instance (where `x y : α`).

 This is so that in a lattice we can use the same underlying constants `max`/`min`
 as in linear orders, while using the more idiomatic notation `x ⊔ y`/`x ⊓ y`.
 Lemmas about the operators `⊔` and `⊓` should use the names `sup` and `inf` respectively.
*/

verus! {

/// Corresponds to Lean's `class HasCompl`.
/// Set / lattice complement
pub trait HasCompl where Self: Sized {
    /// Set / lattice complement
    spec fn compl(self) -> Self;
}

/// Corresponds to Lean's `class Top`.
/// Typeclass for the `⊤` (`\top`) notation
pub trait Top where Self: Sized {
    /// The top (`⊤`, `\top`) element
    spec fn top() -> Self;
}

/// Corresponds to Lean's `class Bot`.
/// Typeclass for the `⊥` (`\bot`) notation
pub trait Bot where Self: Sized {
    /// The bot (`⊥`, `\bot`) element
    spec fn bot() -> Self;
}

/// Corresponds to Lean's `class HImp`.
/// Syntax typeclass for Heyting implication `⇨`.
pub trait HImp where Self: Sized {
    /// Heyting implication `⇨`
    spec fn himp(self, rhs: Self) -> Self;
}

/// Corresponds to Lean's `class SDiff`.
/// The `sdiff` operator, maybe `\` or `─` or `⃥`
pub trait SDiff where Self: Sized {
    /// The sdiff operator
    spec fn sdiff(self, rhs: Self) -> Self;
}

} // verus!
