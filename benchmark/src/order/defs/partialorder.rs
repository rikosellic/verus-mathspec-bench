/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
*/
// mathlib4/Mathlib/Order/Defs/PartialOrder.lean
// Translated to Verus by: Xinyi Wan, 2025.
use vstd::prelude::*;

verus! {

pub trait LE where Self: Sized {
    spec fn le(self, rhs: Self) -> bool;
}

pub trait LT where Self: Sized {
    spec fn lt(self, rhs: Self) -> bool;
}

pub trait Max where Self: Sized {
    spec fn max(self, rhs: Self) -> Self;
}

pub trait Min where Self: Sized {
    spec fn min(self, rhs: Self) -> Self;
}

/// Corresponds to Lean's `class Preorder (α : Type*) extends LE α, LT α`.
/// A preorder is a reflexive, transitive relation `le` with `lt` defined in the obvious way.
pub trait PreOrder: LE + LT where Self: Sized {
    proof fn lemma_le_refl()
        ensures
            forall|x: Self| #[trigger] x.le(x),
    ;

    proof fn lemma_le_trans()
        ensures
            forall|x: Self, y: Self, z: Self| #[trigger] x.le(y) && #[trigger] y.le(z) ==> x.le(z),
    ;

    proof fn lemma_lt_iff_le_not_le()
        ensures
            forall|a: Self, b: Self| #[trigger] a.lt(b) <==> (a.le(b) && !b.le(a)),
    ;
}

/// Corresponds to Lean's `class PartialOrder (α : Type*)`.
/// A partial order is a reflexive, transitive, antisymmetric relation `≤`.
pub trait PartialOrder: PreOrder where Self: Sized {
    proof fn lemma_le_antisymm()
        ensures
            forall|a: Self, b: Self| #[trigger] a.le(b) && #[trigger] b.le(a) ==> a == b,
    ;
}

/*
pub ghost struct TestStruct(pub int);

impl TestStruct {
    pub open spec fn spec_le(self, other: Self) -> bool {
        self.0 <= other.0
    }
    pub open spec fn spec_lt(self, other: Self) -> bool {
        self.0 < other.0
    }
}

impl LE for TestStruct {
    #[verifier::inline]
    open spec fn le(self, rhs: Self) -> bool {
        self.spec_le(rhs)
    }
}

impl LT for TestStruct {
    #[verifier::inline]
    open spec fn lt(self, rhs: Self) -> bool {
        self.spec_lt(rhs)
    }
}

impl PreOrder for TestStruct {
    proof fn lemma_le_refl()
    ensures forall |x: Self| x<=x
    {
    }

    proof fn lemma_le_trans()
    ensures forall |x: Self, y: Self, z: Self|
     x<=y && y<=z ==> x<=z
    {
    }

    proof fn lemma_lt_iff_le_not_le()
    ensures forall |a: Self, b: Self|
     a<b <==> a<=b && ! (b<=a)
    {
    }
}

impl TestStruct {
    pub proof fn test(a: TestStruct, b: TestStruct, c: TestStruct)
    requires a<b, b<c,
    ensures a!=b
    {
    }
}*/
} // verus!
