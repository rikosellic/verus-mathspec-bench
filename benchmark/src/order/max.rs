// SPDX-License-Identifier: Apache-2.0
//
// Copyright (c) 2014 Jeremy Avigad. All rights reserved.
// Released under the Apache License, Version 2.0 as described in the file LICENSE.
// Authors: Jeremy Avigad, Yury Kudryashov, Yaël Dillies
//
// Copyright (c) 2025 Xinyi Wan. All rights reserved.
//
// This file is a Verus transcription of Mathlib/Order/Max.lean originally written in Lean 4,
// with adaptations and modifications by Xinyi Wan (2025).
// Source: https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Order/Max.lean
use crate::order::defs::partialorder::*;
use vstd::prelude::*;

/* # Minimal/maximal and bottom/top elements

This file defines predicates for elements to be minimal/maximal or bottom/top and typeclasses
saying that there are no such elements.

## Predicates

* `IsBot`: An element is *bottom* if all elements are greater than it.
* `IsTop`: An element is *top* if all elements are less than it.
* `IsMin`: An element is *minimal* if no element is strictly less than it.
* `IsMax`: An element is *maximal* if no element is strictly greater than it.

See also `isBot_iff_isMin` and `isTop_iff_isMax` for the equivalences in a (co)directed order.

## Typeclasses

* `NoBotOrder`: An order without bottom elements.
* `NoTopOrder`: An order without top elements.
* `NoMinOrder`: An order without minimal elements.
* `NoMaxOrder`: An order without maximal elements. */

verus! {

/// Corresponds to Lean's `class NoBotOrder`.
/// Order without bottom elements.
pub trait NoBotOrder: LE where Self: Sized {
    /// For each term `a`, there is some `b` which is either incomparable or strictly smaller.
    /// ∃ b, ¬a ≤ b
    proof fn lemma_exists_not_ge(a: Self)
        ensures
            exists|b: Self| !a.le(b),
    ;
}

/// Corresponds to Lean's `class NoTopOrder`.
/// Order without top elements.
pub trait NoTopOrder: LE where Self: Sized {
    /// For each term `a`, there is some `b` which is either incomparable or strictly larger.
    /// ∃ b, ¬b ≤ a
    proof fn lemma_exists_not_le(a: Self)
        ensures
            exists|b: Self| !b.le(a),
    ;
}

/// Corresponds to Lean's `class NoMinOrder`.
/// Order without minimal elements. Sometimes called coinitial or dense.
pub trait NoMinOrder: LT where Self: Sized {
    /// For each term `a`, there is some strictly smaller `b`.
    /// ∃ b, b < a
    proof fn lemma_exists_lt(a: Self)
        ensures
            exists|b: Self| b.lt(a),
    ;
}

/// Corresponds to Lean's `class NoMaxOrder`.
/// Order without maximal elements. Sometimes called cofinal.
pub trait NoMaxOrder: LT where Self: Sized {
    /// For each term `a`, there is some strictly greater `b`.
    /// ∃ b, a < b
    proof fn lemma_exists_gt(a: Self)
        ensures
            exists|b: Self| a.lt(b),
    ;
}

/// Corresponds to Lean's `instance [Preorder α] [NoMinOrder α] : NoBotOrder α`
impl<T: PreOrder + NoMinOrder> NoBotOrder for T {
    /// ∀ a, ∃ b, ¬a ≤ b
    proof fn lemma_exists_not_ge(a: Self)
        ensures
            exists|b: Self| !a.le(b),
    {
        Self::lemma_exists_lt(a);
        let b = choose|b: Self| b.lt(a);
        assert(!a.le(b)) by {
            Self::lemma_lt_iff_le_not_le();
        };
    }
}

impl<T: PreOrder + NoMaxOrder> NoTopOrder for T {
    /// ∀ a, ∃ b, ¬(b ≤ a)
    proof fn lemma_exists_not_le(a: Self)
        ensures
            exists|b: Self| !b.le(a),
    {
        Self::lemma_exists_gt(a);
        let b = choose|b: Self| a.lt(b);
        assert(!b.le(a)) by {
            Self::lemma_lt_iff_le_not_le();
        };
    }
}

/// `a : α` is a bottom element of `α` if it is less than or equal to any other element of `α`.
/// This predicate is roughly an unbundled version of `OrderBot`, except that a preorder may have
/// several bottom elements. When `α` is linear, this is useful to make a case disjunction on
/// `NoMinOrder α` within a proof.
pub open spec fn IsBot<T: LE>(a: T) -> bool {
    forall|b: T| a.le(b)
}

/// `a : α` is a top element of `α` if it is greater than or equal to any other element of `α`.
/// This predicate is roughly an unbundled version of `OrderBot`, except that a preorder may have
/// several top elements. When `α` is linear, this is useful to make a case disjunction on
/// `NoMaxOrder α` within a proof.
pub open spec fn IsTop<T: LE>(a: T) -> bool {
    forall|b: T| b.le(a)
}

/// `a` is a minimal element of `α` if no element is strictly less than it. We spell it without `<`
/// to avoid having to convert between `≤` and `<`. Instead, `isMin_iff_forall_not_lt` does the
/// conversion.
pub open spec fn IsMin<T: LE>(a: T) -> bool {
    forall|b: T| b.le(a) ==> a.le(b)
}

/// `a` is a maximal element of `α` if no element is strictly greater than it. We spell it without
/// `<` to avoid having to convert between `≤` and `<`. Instead, `isMax_iff_forall_not_lt` does the
/// conversion.
pub open spec fn IsMax<T: LE>(a: T) -> bool {
    forall|b: T| a.le(b) ==> b.le(a)
}

/// IsTop i => (IsMax j <=> j = i)
proof fn lemma_IsTop_isMax_iff<T: PartialOrder>(i: T, j: T)
    requires
        IsTop(i),
    ensures
        IsMax(j) <==> (j == i),
{
    T::lemma_le_antisymm();
    T::lemma_le_refl();
    T::lemma_le_trans();

    if IsMax(j) {
        assert(j.le(i));
        assert(i.le(j));
    }
}

/// IsBot i => (IsMin j <=> j = i)
/// IsBot i ==> (IsMin j ↔ j = i)
proof fn lemma_IsBot_isMin_iff<T: PartialOrder>(i: T, j: T)
    requires
        IsBot(i),
    ensures
        IsMin(j) <==> (j == i),
{
    T::lemma_le_antisymm();
    T::lemma_le_refl();
    T::lemma_le_trans();

    if IsMin(j) {
        assert(i.le(j));
        assert(j.le(i));
        assert(j == i);
    }
}

/// IsBot a => b ≤ a => IsBot b
proof fn lemma_IsBot_mono<T: PreOrder>(a: T, b: T)
    requires
        IsBot(a),
        b.le(a),
    ensures
        IsBot(b),
{
    T::lemma_le_trans();

    assert forall|x: T| b.le(x) by {
        assert(a.le(x));
        assert(b.le(x));
    };
}

/// IsTop a => a ≤ b => IsTop b
proof fn lemma_IsTop_mono<T: PreOrder>(a: T, b: T)
    requires
        IsTop(a),
        a.le(b),
    ensures
        IsTop(b),
{
    T::lemma_le_trans();

    assert forall|x: T| x.le(b) by {
        assert(x.le(a));
        assert(x.le(b));
    };
}

/// IsMin a => b ≤ a => IsMin b
proof fn lemma_IsMin_mono<T: PreOrder>(a: T, b: T)
    requires
        IsMin(a),
        b.le(a),
    ensures
        IsMin(b),
{
    T::lemma_le_trans();

    assert forall|c: T| c.le(b) implies b.le(c) by {
        assert(c.le(a));
        assert(a.le(c));
        assert(b.le(c));
    };
}

/// IsMax a => a ≤ b => IsMax b
proof fn lemma_IsMax_mono<T: PreOrder>(a: T, b: T)
    requires
        IsMax(a),
        a.le(b),
    ensures
        IsMax(b),
{
    T::lemma_le_trans();

    assert forall|c: T| b.le(c) implies c.le(b) by {
        assert(a.le(c));
        assert(c.le(a));
        assert(c.le(b));
    };
}

/// IsMin a <=> ∀ b, ¬(b < a)
proof fn lemma_isMin_iff_forall_not_lt<T: PreOrder>(a: T)
    ensures
        IsMin(a) <==> (forall|b: T| !b.lt(a)),
{
    T::lemma_lt_iff_le_not_le();

    if forall|b: T| !b.lt(a) {
        assert(IsMin(a)) by {
            assert forall|b: T| b.le(a) implies a.le(b) by {
                if !a.le(b) {
                    assert(b.lt(a));
                    assert(false);
                }
            };
        };
    }
}

/// IsMax a <=> ∀ b, ¬(a < b)
proof fn lemma_isMax_iff_forall_not_lt<T: PreOrder>(a: T)
    ensures
        IsMax(a) <==> (forall|b: T| !a.lt(b)),
{
    T::lemma_lt_iff_le_not_le();

    if forall|b: T| !a.lt(b) {
        assert(IsMax(a)) by {
            assert forall|b: T| a.le(b) implies b.le(a) by {
                if !b.le(a) {
                    assert(a.lt(b));
                    assert(false);
                }
            };
        };
    }
}

/// ¬IsMin a <=> ∃ b, b < a
proof fn lemma_not_isMin_iff<T: PreOrder>(a: T)
    ensures
        !IsMin(a) <==> (exists|b: T| b.lt(a)),
{
    T::lemma_lt_iff_le_not_le();

    if !IsMin(a) {
        assert(exists|b: T| !(b.le(a) ==> a.le(b)));
        let b = choose|b: T| !(b.le(a) ==> a.le(b));
        assert(b.le(a) && !a.le(b));
        assert(b.lt(a));
    }
}

/// ¬IsMax a ↔ ∃ b, a < b
proof fn lemma_not_isMax_iff<T: PreOrder>(a: T)
    ensures
        !IsMax(a) <==> (exists|b: T| a.lt(b)),
{
    T::lemma_lt_iff_le_not_le();

    if !IsMax(a) {
        assert(exists|b: T| !(a.le(b) ==> b.le(a)));
        let b = choose|b: T| !(a.le(b) ==> b.le(a));
        assert(a.le(b) && !b.le(a));
        assert(a.lt(b));
    }
}

/// [NoMinOrder α] => ¬IsMin a
proof fn lemma_not_isMin<T: PreOrder + NoMinOrder>(a: T)
    ensures
        !IsMin(a),
{
    lemma_not_isMin_iff(a);
    T::lemma_exists_lt(a);
}

/// [NoMaxOrder α] => ¬IsMax a
proof fn lemma_not_isMax<T: PreOrder + NoMaxOrder>(a: T)
    ensures
        !IsMax(a),
{
    lemma_not_isMax_iff(a);
    T::lemma_exists_gt(a);
}

} // verus!
