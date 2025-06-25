/*
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
*/
// Mathlib/Order/BoundedOrder/Basic.lean
// Translated to Verus by: Xinyi Wan, 2025.
use crate::order::{defs::partialorder::*, notation::*};
use vstd::prelude::*;

/* # ⊤ and ⊥, bounded lattices and variants

This file defines top and bottom elements (greatest and least elements) of a type, the bounded
variants of different kinds of lattices, sets up the typeclass hierarchy between them and provides
instances for `Prop` and `fun`.

## Main declarations

* `<Top/Bot> α`: Typeclasses to declare the `⊤`/`⊥` notation.
* `Order<Top/Bot> α`: Order with a top/bottom element.
* `BoundedOrder α`: Order with a top and bottom element.*/

verus! {

/// ### Top, bottom element
/// Corresponds to Lean's `class OrderTop`.
/// An order is an `OrderTop` if it has a greatest element.
/// We state this using a data mixin, holding the value of `⊤` and the greatest element constraint.
pub trait OrderTop: Top + LE where Self: Sized {
    /// `⊤` is the greatest element
    /// ∀ a : α, a ≤ ⊤
    proof fn lemma_le_top()
        ensures
            forall|a: Self| #[trigger] a.le(Self::top()),
    ;
}

} // verus!
