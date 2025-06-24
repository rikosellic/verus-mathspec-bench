/*
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury Kudryashov
*/
// Mathlib/Order/Bounds/Defs.lean
// Translated to Verus by: Xinyi Wan, 2025.
use crate::order::defs::partialorder::*;
use vstd::prelude::*;

/* # Definitions about upper/lower bounds

In this file we define:
* `upperBounds`, `lowerBounds` : the set of upper bounds (resp., lower bounds) of a set;
* `BddAbove s`, `BddBelow s` : the set `s` is bounded above (resp., below), i.e., the set of upper
  (resp., lower) bounds of `s` is nonempty;
* `IsLeast s a`, `IsGreatest s a` : `a` is a least (resp., greatest) element of `s`;
  for a partial order, it is unique if exists;
* `IsLUB s a`, `IsGLB s a` : `a` is a least upper bound (resp., a greatest lower bound)
  of `s`; for a partial order, it is unique if exists.
* `IsCofinal s`: for every `a`, there exists a member of `s` greater or equal to it.
* `IsCofinalFor s t` : for all `a ∈ s` there exists `b ∈ t` such that `a ≤ b`
* `IsCoinitialFor s t` : for all `a ∈ s` there exists `b ∈ t` such that `b ≤ a` */

verus! {

/// The set of upper bounds of a set.
/// { x | ∀ ⦃a⦄, a ∈ s → a ≤ x }
#[allow(non_snake_case)]
pub open spec fn upperBounds<T: LE>(s: Set<T>) -> Set<T> {
    Set::new(|x: T| s.all(|a: T| a.le(x)))
}

/// The set of lower bounds of a set.
#[allow(non_snake_case)]
pub open spec fn lowerBounds<T: LE>(s: Set<T>) -> Set<T> {
    Set::new(|x: T| s.all(|a: T| x.le(a)))
}

/// A set is bounded above if there exists an upper bound.
#[allow(non_snake_case)]
pub open spec fn BddAbove<T: LE>(s: Set<T>) -> bool {
    !upperBounds(s).is_empty()
}

/// A set is bounded below if there exists a lower bound.
#[allow(non_snake_case)]
pub open spec fn BddBelow<T: LE>(s: Set<T>) -> bool {
    !lowerBounds(s).is_empty()
}

/// `a` is a least element of a set `s`; for a partial order, it is unique if exists.
#[allow(non_snake_case)]
pub open spec fn IsLeast<T: LE>(s: Set<T>, a: T) -> bool {
    s.contains(a) && lowerBounds(s).contains(a)
}

/// `a` is a greatest element of a set `s`; for a partial order, it is unique if exists.
#[allow(non_snake_case)]
pub open spec fn IsGreatest<T: LE>(s: Set<T>, a: T) -> bool {
    s.contains(a) && upperBounds(s).contains(a)
}

/// `a` is a least upper bound of a set `s`; for a partial order, it is unique if exists.
#[allow(non_snake_case)]
pub open spec fn IsLUB<T: LE>(s: Set<T>, a: T) -> bool {
    IsLeast(upperBounds(s), a)
}

/// `a` is a greatest lower bound of a set `s`; for a partial order, it is unique if exists.
#[allow(non_snake_case)]
pub open spec fn IsGLB<T: LE>(s: Set<T>, a: T) -> bool {
    IsGreatest(lowerBounds(s), a)
}

/// A set `s` is said to be cofinal for a set `t` if, for all `a ∈ s` there exists `b ∈ t`
/// such that `a ≤ b`.
/// ∀ ⦃a⦄, a ∈ s → ∃ b ∈ t, a ≤ b
#[allow(non_snake_case)]
pub open spec fn IsCofinalFor<T: LE>(s: Set<T>, t: Set<T>) -> bool {
    s.all(|a: T| t.any(|b: T| a.le(b)))
}

/// A set `s` is said to be coinitial for a set `t` if, for all `a ∈ s` there exists `b ∈ t`
/// such that `b ≤ a`.
/// ∀ ⦃a⦄, a ∈ s → ∃ b ∈ t, b ≤ a
#[allow(non_snake_case)]
pub open spec fn IsCoinitialFor<T: LE>(s: Set<T>, t: Set<T>) -> bool {
    s.all(|a: T| t.any(|b: T| b.le(a)))
}

/// A set is cofinal when for every `x : α` there exists `y ∈ s` with `x ≤ y`.
/// ∀ x, ∃ y ∈ s, x ≤ y
#[allow(non_snake_case)]
pub open spec fn IsCofinal<T: LE>(s: Set<T>) -> bool {
    s.all(|x: T| s.any(|y: T| x.le(y)))
}

} // verus!
