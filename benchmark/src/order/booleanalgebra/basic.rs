/*
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Bryan Gin-ge Chen
*/
// Mathlib/Order/BooleanAlgebra/Basic.lean
// Translated to Verus by: Yuwei LIU, 2025.
use crate::order::{booleanalgebra::defs::*, lattice::*, notation::*};
use vstd::prelude::*;

verus! {

// x ⊓ y ⊔ x \ y == x
// @[simp]
pub proof fn lemma_sup_inf_sdiff<T: GeneralizedBooleanAlgebra>(x: T, y: T)
    ensures
        x.inf(y).sup(x.sdiff(y)) == x,
{
    T::lemma_sup_inf_sdiff();
}

// x ⊓ y ⊓ x \ y == ⊥
// @[simp]
pub proof fn lemma_inf_inf_sdiff<T: GeneralizedBooleanAlgebra>(x: T, y: T)
    ensures
        x.inf(y).inf(x.sdiff(y)) == T::bot(),
{
    T::lemma_inf_inf_sdiff();
}

// x \ y ⊔ x ⊓ y == x
// @[simp]
pub proof fn lemma_sup_sdiff_inf<T: GeneralizedBooleanAlgebra>(x: T, y: T)
    ensures
        x.sdiff(y).sup(x.inf(y)) == x,
{
    T::lemma_sup_comm(x.sdiff(y), x.inf(y));
    lemma_sup_inf_sdiff(x, y);
}

// x \ y ⊓ (x ⊓ y) == ⊥
// @[simp]
pub proof fn lemma_inf_sdiff_inf<T: GeneralizedBooleanAlgebra>(x: T, y: T)
    ensures
        x.sdiff(y).inf(x.inf(y)) == T::bot(),
{
    T::lemma_inf_comm(x.sdiff(y), x.inf(y));
    lemma_inf_inf_sdiff(x, y);
}

// -- see Note [lower instance priority]
// instance (priority := 100) GeneralizedBooleanAlgebra.toOrderBot
// bot_le a := by
//   rw [← inf_inf_sdiff a a, inf_assoc]
//   exact inf_le_left
pub proof fn lemma_bot_le<T: GeneralizedBooleanAlgebra + SemilatticeInf>(a: T)
    ensures
        T::bot().le(a),
{
    lemma_inf_inf_sdiff(a, a);
    T::lemma_inf_le_left();
    T::lemma_inf_idem(a);
}

} // verus!
