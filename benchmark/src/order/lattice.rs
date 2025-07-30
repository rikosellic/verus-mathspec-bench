// SPDX-License-Identifier: Apache-2.0
//
// Copyright (c) 2017 Johannes Hölzl. All rights reserved.
// Released under the Apache License, Version 2.0 as described in the file LICENSE.
// Authors: Johannes Hölzl
//
// Copyright (c) 2025 Xinyi Wan. All rights reserved.
//
// This file is a Verus transcription of mathlib4/Mathlib/Order/Lattice.lean originally written in Lean 4,
// with adaptations and modifications by Xinyi Wan (2025).
// Source: https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Order/Lattice.lean
use crate::order::defs::partialorder::*;
use vstd::prelude::*;
/*
Semilattices are partially ordered sets with join (least upper bound, or `sup`) or meet (greatest
lower bound, or `inf`) operations. Lattices are posets that are both join-semilattices and
meet-semilattices.

Distributive lattices are lattices which satisfy any of four equivalent distributivity properties,
of `sup` over `inf`, on the left or on the right.
*/

verus! {

/// Corresponds to Lean's `class SemilatticeSup (α : Type*) extends PartialOrder α`.
/// A `SemilatticeSup` is a join-semilattice, that is, a partial order
/// with a join (a.k.a. lub / least upper bound, sup / supremum) operation
/// `⊔` which is the least element larger than both factors. -/
pub trait SemilatticeSup: PartialOrder where Self: Sized {
    /// The binary supremum, used to derive `Max α`
    spec fn sup(self, rhs: Self) -> Self;

    /// The supremum is an upper bound on the first argument
    /// ∀ a b : α, a ≤ a ⊔ b
    proof fn lemma_le_sup_left()
        ensures
            forall|a: Self, b: Self| #[trigger] a.le(a.sup(b)),
    ;

    /// The supremum is an upper bound on the second argument
    /// ∀ a b : α, b ≤ a ⊔ b
    proof fn lemma_le_sup_right()
        ensures
            forall|a: Self, b: Self| #[trigger] b.le(a.sup(b)),
    ;

    /// The supremum is the *least* upper bound
    /// ∀ a b c : α, a ≤ c => b ≤ c => a ⊔ b ≤ c
    proof fn lemma_sup_le()
        ensures
            forall|a: Self, b: Self, c: Self| a.le(c) && b.le(c) ==> #[trigger] a.sup(b).le(c),
    ;

    // Derived lemmas
    /// c <= a => c <= a ⊔ b
    proof fn lemma_le_sup_of_le_left(a: Self, b: Self, c: Self)
        requires
            c.le(a),
        ensures
            c.le(a.sup(b)),
    {
        assert(a.le(a.sup(b))) by { Self::lemma_le_sup_left() };
        assert(c.le(a) ==> a.le(a.sup(b)) ==> c.le(a.sup(b))) by {
            Self::lemma_le_trans();
        };
    }

    /// c <= b => c <= a ⊔ b
    proof fn lemma_le_sup_of_le_right(a: Self, b: Self, c: Self)
        requires
            c.le(b),
        ensures
            c.le(a.sup(b)),
    {
        assert(b.le(a.sup(b))) by {
            Self::lemma_le_sup_right();
        };
        assert(c.le(b) ==> b.le(a.sup(b)) ==> c.le(a.sup(b))) by {
            Self::lemma_le_trans();
        };
    }

    /// c < a => c < a ⊔ b
    proof fn lemma_lt_sup_of_lt_left(a: Self, b: Self, c: Self)
        requires
            c.lt(a),
        ensures
            c.lt(a.sup(b)),
    {
        Self::lemma_lt_iff_le_not_le();
        Self::lemma_le_sup_left();
        Self::lemma_le_trans();

        assert(c.le(a));
        assert(a.le(a.sup(b)));
        assert(c.le(a.sup(b)));

        if a.sup(b).le(c) {
            assert(a.le(c));
            assert(!a.le(c));
        }
        assert(c.lt(a.sup(b)));
    }

    /// c < b => c < a ⊔ b
    proof fn lemma_lt_sup_of_lt_right(a: Self, b: Self, c: Self)
        requires
            c.lt(b),
        ensures
            c.lt(a.sup(b)),
    {
        Self::lemma_lt_iff_le_not_le();
        Self::lemma_le_sup_right();
        Self::lemma_le_trans();

        assert(c.le(b));
        assert(b.le(a.sup(b)));
        assert(c.le(a.sup(b)));

        if a.sup(b).le(c) {
            assert(b.le(c));
            assert(!b.le(c));
            assert(false);
        }
        assert(c.lt(a.sup(b)));
    }

    /// a ⊔ b ≤ c <==> a ≤ c ∧ b ≤ c
    proof fn lemma_sup_le_iff(a: Self, b: Self, c: Self)
        ensures
            (a.sup(b).le(c)) <==> (a.le(c) && b.le(c)),
    {
        Self::lemma_le_sup_left();
        Self::lemma_le_sup_right();
        Self::lemma_sup_le();
        Self::lemma_le_trans();

        assert((a.sup(b).le(c)) <==> (a.le(c) && b.le(c))) by {
            if a.sup(b).le(c) {
                assert(a.le(a.sup(b)));
                assert(a.le(c));
                assert(b.le(a.sup(b)));
                assert(b.le(c));
            }
            if a.le(c) && b.le(c) {
                assert(a.sup(b).le(c));
            }
        };
    }

    /// a ⊔ b == a <==> b ≤ a
    proof fn lemma_sup_eq_left(a: Self, b: Self)
        ensures
            (a.sup(b) == a) <==> b.le(a),
    {
        Self::lemma_le_sup_left();
        Self::lemma_sup_le_iff(a, b, a);
        Self::lemma_le_antisymm();
        Self::lemma_le_refl();

        assert((a.sup(b) == a) <==> b.le(a)) by {
            if a.sup(b) == a {
                assert(a.sup(b).le(a));
                assert(b.le(a));
            }
            if b.le(a) {
                assert(a.le(a));
                assert(a.sup(b).le(a));
                assert(a.le(a.sup(b)));
                assert(a.sup(b) == a);
            }
        };
    }

    /// a ⊔ b == b <==> a ≤ b
    proof fn lemma_sup_eq_right(a: Self, b: Self)
        ensures
            (a.sup(b) == b) <==> a.le(b),
    {
        Self::lemma_le_sup_left();
        Self::lemma_le_sup_right();
        Self::lemma_sup_le_iff(a, b, b);
        Self::lemma_le_antisymm();
        Self::lemma_le_refl();

        assert((a.sup(b) == b) <==> a.le(b)) by {
            if a.sup(b) == b {
                assert(a.le(a.sup(b)));
                assert(a.le(b));
            }
            if a.le(b) {
                assert(b.le(b));
                assert(a.sup(b).le(b));
                assert(b.le(a.sup(b)));
                assert(a.sup(b) == b);
            }
        };
    }

    /// a == a ⊔ b <==> a ≤ b
    proof fn lemma_left_eq_sup(a: Self, b: Self)
        ensures
            (a == a.sup(b)) <==> b.le(a),
    {
        Self::lemma_sup_eq_left(a, b);
    }

    /// b == a ⊔ b <==> a ≤ b
    proof fn lemma_right_eq_sup(a: Self, b: Self)
        ensures
            (b == a.sup(b)) <==> a.le(b),
    {
        Self::lemma_sup_eq_right(a, b);
    }

    /// a < a ⊔ b <==> !b ≤ a
    proof fn lemma_left_lt_sup(a: Self, b: Self)
        ensures
            a.lt(a.sup(b)) <==> !b.le(a),
    {
        Self::lemma_lt_iff_le_not_le();
        Self::lemma_le_sup_left();
        Self::lemma_le_antisymm();
        Self::lemma_left_eq_sup(a, b);

        assert(a.lt(a.sup(b)) <==> !b.le(a)) by {
            if a.lt(a.sup(b)) {
                if b.le(a) {
                    assert(a == a.sup(b));
                    assert(a.lt(a));
                    assert(false);
                }
            }
            if !b.le(a) {
                assert(a.le(a.sup(b)));

                if a.sup(b).le(a) {
                    assert(a.sup(b) == a);
                    assert(b.le(a));
                    assert(false);
                }
                assert(a.lt(a.sup(b)));
            }
        };
    }

    /// b < a ⊔ b <==> !a ≤ b
    proof fn lemma_right_lt_sup(a: Self, b: Self)
        ensures
            b.lt(a.sup(b)) <==> !a.le(b),
    {
        Self::lemma_lt_iff_le_not_le();
        Self::lemma_le_sup_right();
        Self::lemma_le_antisymm();
        Self::lemma_right_eq_sup(a, b);

        assert(b.lt(a.sup(b)) <==> !a.le(b)) by {
            if b.lt(a.sup(b)) {
                if a.le(b) {
                    assert(b == a.sup(b));
                    assert(b.lt(b));
                    assert(false);
                }
            }
            if !a.le(b) {
                assert(b.le(a.sup(b)));

                if a.sup(b).le(b) {
                    assert(a.sup(b) == b);
                    assert(a.le(b));
                    assert(false);
                }
                assert(b.lt(a.sup(b)));
            }
        };
    }

    /// a <= b <==> ∃ c, b == a ⊔ c
    proof fn lemma_le_iff_exists_sup(a: Self, b: Self)
        ensures
            a.le(b) <==> exists|c: Self| b == a.sup(c),
    {
        Self::lemma_sup_eq_right(a, b);
        Self::lemma_le_sup_left();
    }

    /// a <= b => c <= d => a ⊔ c <= b ⊔ d
    proof fn lemma_sup_le_sup(a: Self, b: Self, c: Self, d: Self)
        requires
            a.le(b),
            c.le(d),
        ensures
            a.sup(c).le(b.sup(d)),
    {
        Self::lemma_le_sup_left();
        Self::lemma_le_sup_right();
        Self::lemma_sup_le();
        Self::lemma_le_trans();

        assert(b.le(b.sup(d)));
        assert(a.le(b.sup(d)));

        assert(d.le(b.sup(d)));
        assert(c.le(b.sup(d)));

        assert(a.sup(c).le(b.sup(d)));
    }

    /// a <= b ==> c ⊔ a <= c ⊔ b
    proof fn lemma_sup_le_sup_left(a: Self, b: Self, c: Self)
        requires
            a.le(b),
        ensures
            c.sup(a).le(c.sup(b)),
    {
        Self::lemma_le_refl();
        Self::lemma_sup_le_sup(c, c, a, b);

        assert(c.le(c));

        assert(c.sup(a).le(c.sup(b)));
    }

    /// a ⊔ a == a
    proof fn lemma_sup_idem(a: Self)
        ensures
            a.sup(a) == a,
    {
        Self::lemma_sup_eq_right(a, a);
        Self::lemma_le_refl();
    }

    /// a ⊔ b == b ⊔ a
    proof fn lemma_sup_comm(a: Self, b: Self)
        ensures
            a.sup(b) == b.sup(a),
    {
        Self::lemma_le_antisymm();
        Self::lemma_sup_le_iff(a, b, b.sup(a));
        Self::lemma_sup_le_iff(b, a, a.sup(b));
        Self::lemma_le_sup_left();
        Self::lemma_le_sup_right();
    }

    /// a ⊔ b ⊔ c == a ⊔ (b ⊔ c)
    proof fn lemma_sup_assoc(a: Self, b: Self, c: Self)
        ensures
            a.sup(b).sup(c) == a.sup(b.sup(c)),
    {
        Self::lemma_le_antisymm();
        Self::lemma_sup_le();
        Self::lemma_le_sup_left();
        Self::lemma_le_sup_right();
        Self::lemma_le_trans();

        assert(a.sup(b).sup(c) == a.sup(b.sup(c))) by {
            let lhs = a.sup(b).sup(c);
            let rhs = a.sup(b.sup(c));
            assert(lhs.le(rhs)) by {
                assert(a.sup(b).le(rhs)) by {
                    assert(a.le(rhs));
                    assert(b.le(b.sup(c)));
                    assert(b.sup(c).le(rhs));
                    assert(b.le(rhs));
                };

                assert(c.le(rhs)) by {
                    assert(c.le(b.sup(c)));
                    assert(b.sup(c).le(rhs));
                };
            };
            assert(rhs.le(lhs)) by {
                assert(a.le(lhs)) by {
                    assert(a.le(a.sup(b)));
                    assert(a.sup(b).le(lhs));
                };
                assert(b.sup(c).le(lhs)) by {
                    assert(b.le(a.sup(b)));
                    assert(a.sup(b).le(lhs));
                    assert(b.le(lhs));
                    assert(c.le(lhs));
                };
            };
        };

    }

    /// a ⊔ b ⊔ c == c ⊔ b ⊔ a
    proof fn lemma_sup_left_right_swap(a: Self, b: Self, c: Self)
        ensures
            a.sup(b).sup(c) == c.sup(b).sup(a),
    {
        Self::lemma_sup_comm(a, b);
        Self::lemma_sup_comm(a, c);
        Self::lemma_sup_comm(b, c);
        Self::lemma_sup_comm(a.sup(b), c);
        Self::lemma_sup_comm(c.sup(b), a);
        Self::lemma_sup_assoc(a, b, c);
        Self::lemma_sup_assoc(b, a, c);
        Self::lemma_sup_assoc(c, b, a);
    }

    /// a ⊔ (a ⊔ b) == a ⊔ b
    proof fn lemma_sup_left_idem(a: Self, b: Self)
        ensures
            a.sup(a.sup(b)) == a.sup(b),
    {
        Self::lemma_sup_assoc(a, a, b);
        Self::lemma_sup_idem(a);
    }

    /// a ⊔ (b ⊔ b) == a ⊔ b
    proof fn lemma_sup_right_idem(a: Self, b: Self)
        ensures
            a.sup(b).sup(b) == a.sup(b),
    {
        Self::lemma_sup_assoc(a, b, b);
        Self::lemma_sup_idem(b);
    }

    /// a ⊔ b ⊔ c == b ⊔ a ⊔ c
    proof fn lemma_sup_left_comm(a: Self, b: Self, c: Self)
        ensures
            a.sup(b.sup(c)) == b.sup(a.sup(c)),
    {
        Self::lemma_sup_assoc(a, b, c);
        Self::lemma_sup_assoc(b, a, c);
        Self::lemma_sup_comm(a, b);
    }

    /// a ⊔ b ⊔ c == a ⊔ c ⊔ b
    proof fn lemma_sup_right_comm(a: Self, b: Self, c: Self)
        ensures
            a.sup(b).sup(c) == a.sup(c).sup(b),
    {
        Self::lemma_sup_assoc(a, b, c);
        Self::lemma_sup_assoc(a, c, b);
        Self::lemma_sup_comm(b, c);
    }

    /// a ⊔ b ⊔ (c ⊔ d) == a ⊔ c ⊔ (b ⊔ d)
    proof fn lemma_sup_sup_sup_comm(a: Self, b: Self, c: Self, d: Self)
        ensures
            a.sup(b).sup(c.sup(d)) == a.sup(c).sup(b.sup(d)),
    {
        Self::lemma_sup_assoc(a, b, c.sup(d));
        Self::lemma_sup_assoc(a, c, b.sup(d));
        Self::lemma_sup_left_comm(b, c, d);
    }

    /// a ⊔ (b ⊔ c) == a ⊔ b ⊔ (a ⊔ c)
    proof fn lemma_sup_sup_distrib_left(a: Self, b: Self, c: Self)
        ensures
            a.sup(b.sup(c)) == a.sup(b).sup(a.sup(c)),
    {
        Self::lemma_sup_sup_sup_comm(a, b, a, c);
        Self::lemma_sup_idem(a);
    }

    /// a ⊔ b ⊔ c == a ⊔ c ⊔ (b ⊔ c)
    proof fn lemma_sup_sup_distrib_right(a: Self, b: Self, c: Self)
        ensures
            a.sup(b).sup(c) == a.sup(c).sup(b.sup(c)),
    {
        Self::lemma_sup_sup_sup_comm(a, c, b, c);
        Self::lemma_sup_idem(c);
    }

    /// b <= a ⊔ c ==> c <= a ⊔ b ==> a ⊔ b == a ⊔ c
    proof fn lemma_sup_congr_left(a: Self, b: Self, c: Self)
        requires
            b.le(a.sup(c)),
            c.le(a.sup(b)),
        ensures
            a.sup(b) == a.sup(c),
    {
        Self::lemma_le_antisymm();
        Self::lemma_sup_le();
        Self::lemma_le_sup_left();

        assert(a.sup(b) == a.sup(c)) by {
            assert(a.sup(b).le(a.sup(c))) by {
                assert(a.le(a.sup(c)));
            };

            assert(a.sup(c).le(a.sup(b))) by {
                assert(a.le(a.sup(b)));
            };
        };
    }

    /// a <= b ⊔ c ==> b <= a ⊔ c ==> a ⊔ c == b ⊔ c
    proof fn lemma_sup_congr_right(a: Self, b: Self, c: Self)
        requires
            a.le(b.sup(c)),
            b.le(a.sup(c)),
        ensures
            a.sup(c) == b.sup(c),
    {
        Self::lemma_le_antisymm();
        Self::lemma_sup_le();
        Self::lemma_le_sup_right();

        assert(a.sup(c) == b.sup(c)) by {
            assert(a.sup(c).le(b.sup(c))) by {
                assert(c.le(b.sup(c)));
            };
            assert(b.sup(c).le(a.sup(c))) by {
                assert(c.le(a.sup(c)));
            };
        };
    }

    /// a ⊔ b == a ⊔ c <==> b <= a ⊔ c ∧ c <= a ⊔ b
    proof fn lemma_sup_eq_sup_iff_left(a: Self, b: Self, c: Self)
        ensures
            (a.sup(b) == a.sup(c)) <==> (b.le(a.sup(c)) && c.le(a.sup(b))),
    {
        Self::lemma_le_sup_right();

        assert((a.sup(b) == a.sup(c)) <==> (b.le(a.sup(c)) && c.le(a.sup(b)))) by {
            if a.sup(b) == a.sup(c) {
                assert(b.le(a.sup(b)));
                assert(b.le(a.sup(c)));

                assert(c.le(a.sup(c)));
                assert(c.le(a.sup(b)));
            }
            if b.le(a.sup(c)) && c.le(a.sup(b)) {
                assert(b.le(a.sup(c)));
                assert(c.le(a.sup(b)));
                Self::lemma_sup_congr_left(a, b, c);
                assert(a.sup(b) == a.sup(c));
            }
        };
    }

    /// a ⊔ c == b ⊔ c <==> a <= b ⊔ c ∧ b <= a ⊔ c
    proof fn lemma_sup_eq_sup_iff_right(a: Self, b: Self, c: Self)
        ensures
            (a.sup(c) == b.sup(c)) <==> (a.le(b.sup(c)) && b.le(a.sup(c))),
    {
        Self::lemma_le_sup_left();
        assert((a.sup(c) == b.sup(c)) <==> (a.le(b.sup(c)) && b.le(a.sup(c)))) by {
            if a.sup(c) == b.sup(c) {
                assert(a.le(a.sup(c)));
                assert(a.le(b.sup(c)));

                assert(b.le(b.sup(c)));
                assert(b.le(a.sup(c)));
            }
            if a.le(b.sup(c)) && b.le(a.sup(c)) {
                assert(a.le(b.sup(c)));
                assert(b.le(a.sup(c)));
                Self::lemma_sup_congr_right(a, b, c);
                assert(a.sup(c) == b.sup(c));
            }
        };
    }

    /// a != b ==> a < a ⊔ b ∨ b < a ⊔ b
    proof fn lemma_ne_lt_sup_or_lt_sup(a: Self, b: Self)
        requires
            a != b,
        ensures
            a.lt(a.sup(b)) || b.lt(a.sup(b)),
    {
        Self::lemma_left_lt_sup(a, b);
        Self::lemma_right_lt_sup(a, b);
        Self::lemma_le_antisymm();
    }
}

/// Corresponds to Lean's `class SemilatticeInf (α : Type u)`.
/// A `SemilatticeInf` is a meet-semilattice, that is, a partial order
/// with a meet (a.k.a. glb / greatest lower bound, inf / infimum) operation
/// `⊓` which is the greatest element smaller than both factors.
pub trait SemilatticeInf: PartialOrder where Self: Sized {
    /// The binary infimum, used to derive `Min α`
    spec fn inf(self, rhs: Self) -> Self;

    /// The infimum is a lower bound on the first argument
    /// ∀ a b : α, a ⊓ b ≤ a
    proof fn lemma_inf_le_left()
        ensures
            forall|a: Self, b: Self| #[trigger] a.inf(b).le(a),
    ;

    /// The infimum is a lower bound on the second argument
    /// ∀ a b : α, a ⊓ b ≤ b
    proof fn lemma_inf_le_right()
        ensures
            forall|a: Self, b: Self| #[trigger] a.inf(b).le(b),
    ;

    /// The infimum is the *greatest* lower bound
    /// ∀ a b c : α, a <= b => a <= c => a <= b ⊓ c
    proof fn lemma_le_inf()
        ensures
            forall|a: Self, b: Self, c: Self| a.le(b) && a.le(c) ==> #[trigger] a.le(b.inf(c)),
    ;

    /// a <= c ==> a ⊓ b <= c
    proof fn lemma_inf_le_of_left_le(a: Self, b: Self, c: Self)
        requires
            a.le(c),
        ensures
            a.inf(b).le(c),
    {
        Self::lemma_inf_le_left();
        Self::lemma_le_trans();

        assert(a.inf(b).le(a));
        assert(a.inf(b).le(c));
    }

    /// b <= c ==> a ⊓ b <= c
    proof fn lemma_inf_le_of_right_le(a: Self, b: Self, c: Self)
        requires
            b.le(c),
        ensures
            a.inf(b).le(c),
    {
        Self::lemma_inf_le_right();
        Self::lemma_le_trans();

        assert(a.inf(b).le(b));
        assert(a.inf(b).le(c));
    }

    /// a < c ==> a ⊓ b < c
    proof fn lemma_inf_lt_of_left_lt(a: Self, b: Self, c: Self)
        requires
            a.lt(c),
        ensures
            a.inf(b).lt(c),
    {
        Self::lemma_inf_le_left();
        Self::lemma_lt_iff_le_not_le();
        Self::lemma_le_trans();

        assert(a.inf(b).le(a));
        assert(a.le(c));
        assert(a.inf(b).le(c));

        if c.le(a.inf(b)) {
            assert(c.le(a));
            assert(!c.le(a));
        }
        assert(a.inf(b).lt(c));
    }

    /// b < c ==> a ⊓ b < c
    proof fn lemma_inf_lt_of_right_lt(a: Self, b: Self, c: Self)
        requires
            b.lt(c),
        ensures
            a.inf(b).lt(c),
    {
        Self::lemma_inf_le_right();
        Self::lemma_lt_iff_le_not_le();
        Self::lemma_le_trans();

        assert(a.inf(b).le(b));
        assert(b.le(c));
        assert(a.inf(b).le(c));

        if c.le(a.inf(b)) {
            assert(c.le(b));
            assert(!c.le(b));
        }
        assert(a.inf(b).lt(c));
    }

    /// a <= b ⊓ c <==> a <= b ∧ a <= c
    proof fn lemma_le_inf_iff(a: Self, b: Self, c: Self)
        ensures
            a.le(b.inf(c)) <==> (a.le(b) && a.le(c)),
    {
        Self::lemma_inf_le_left();
        Self::lemma_inf_le_right();
        Self::lemma_le_inf();
        Self::lemma_le_trans();

        assert(a.le(b.inf(c)) <==> (a.le(b) && a.le(c))) by {
            if a.le(b.inf(c)) {
                assert(b.inf(c).le(b));
                assert(a.le(b));

                assert(b.inf(c).le(c));
                assert(a.le(c));
            }
            if a.le(b) && a.le(c) {
                assert(a.le(b.inf(c)));
            }
        };
    }

    /// a ⊓ b == a <==> a <= b
    proof fn lemma_inf_eq_left(a: Self, b: Self)
        ensures
            (a.inf(b) == a) <==> a.le(b),
    {
        Self::lemma_le_antisymm();
        Self::lemma_le_inf_iff(a, a, b);
        Self::lemma_inf_le_left();
        Self::lemma_le_refl();

        assert((a.inf(b) == a) <==> a.le(b)) by {
            if a.inf(b) == a {
                assert(a.le(a.inf(b)));
                assert(a.le(b));
            }
            if a.le(b) {
                assert(a.le(a));
                assert(a.le(a.inf(b)));
                assert(a.inf(b).le(a));
                assert(a.inf(b) == a);
            }
        };
    }

    /// a ⊓ b == b <==> b <= a
    proof fn lemma_inf_eq_right(a: Self, b: Self)
        ensures
            (a.inf(b) == b) <==> b.le(a),
    {
        Self::lemma_le_antisymm();
        Self::lemma_le_inf_iff(b, a, b);
        Self::lemma_inf_le_right();
        Self::lemma_le_refl();

        assert((a.inf(b) == b) <==> b.le(a)) by {
            if a.inf(b) == b {
                assert(b.le(a.inf(b)));
                assert(b.le(a));
            }
            if b.le(a) {
                assert(b.le(b));
                assert(b.le(a.inf(b)));
                assert(a.inf(b).le(b));
                assert(a.inf(b) == b);
            }
        };
    }

    /// a == a ⊓ b <==> a <= b
    proof fn lemma_left_eq_inf(a: Self, b: Self)
        ensures
            (a == a.inf(b)) <==> a.le(b),
    {
        Self::lemma_inf_eq_left(a, b);
    }

    /// b == a ⊓ b <==> b <= a
    proof fn lemma_right_eq_inf(a: Self, b: Self)
        ensures
            (b == a.inf(b)) <==> b.le(a),
    {
        Self::lemma_inf_eq_right(a, b);
    }

    /// a ⊓ b < a <==> !a <= b
    proof fn lemma_inf_lt_left(a: Self, b: Self)
        ensures
            a.inf(b).lt(a) <==> !a.le(b),
    {
        Self::lemma_lt_iff_le_not_le();
        Self::lemma_inf_le_left();
        Self::lemma_le_antisymm();
        Self::lemma_inf_eq_left(a, b);

        assert(a.inf(b).lt(a) <==> !a.le(b)) by {
            if a.inf(b).lt(a) {
                if a.le(b) {
                    assert(a.inf(b) == a);
                    assert(a.lt(a));
                    assert(false);
                }
            }
            if !a.le(b) {
                assert(a.inf(b).le(a));

                if a.le(a.inf(b)) {
                    assert(a.inf(b) == a);
                    assert(a.le(b));
                    assert(false);
                }
                assert(a.inf(b).lt(a));
            }
        };
    }

    /// a ⊓ b < b <==> !b <= a
    proof fn lemma_inf_lt_right(a: Self, b: Self)
        ensures
            a.inf(b).lt(b) <==> !b.le(a),
    {
        Self::lemma_lt_iff_le_not_le();
        Self::lemma_inf_le_right();
        Self::lemma_le_antisymm();
        Self::lemma_inf_eq_right(a, b);

        assert(a.inf(b).lt(b) <==> !b.le(a)) by {
            if a.inf(b).lt(b) {
                if b.le(a) {
                    assert(a.inf(b) == b);
                    assert(b.lt(b));
                    assert(false);
                }
            }
            if !b.le(a) {
                assert(a.inf(b).le(b));

                if b.le(a.inf(b)) {
                    assert(a.inf(b) == b);
                    assert(b.le(a));
                    assert(false);
                }
                assert(a.inf(b).lt(b));
            }
        };
    }

    /// a != b ==> a ⊓ b < a ∨ a ⊓ b < b
    proof fn lemma_inf_lt_left_or_right(a: Self, b: Self)
        requires
            a != b,
        ensures
            a.inf(b).lt(a) || a.inf(b).lt(b),
    {
        Self::lemma_inf_lt_left(a, b);
        Self::lemma_inf_lt_right(a, b);
        Self::lemma_le_antisymm();
    }

    /// a <= b ==> c <= d ==> a ⊓ c <= b ⊓ d
    proof fn lemma_inf_le_inf(a: Self, b: Self, c: Self, d: Self)
        requires
            a.le(b),
            c.le(d),
        ensures
            a.inf(c).le(b.inf(d)),
    {
        Self::lemma_inf_le_left();
        Self::lemma_inf_le_right();
        Self::lemma_le_inf();
        Self::lemma_le_trans();

        assert(a.inf(c).le(a));
        assert(a.inf(c).le(b));

        assert(a.inf(c).le(c));
        assert(a.inf(c).le(d));

        assert(a.inf(c).le(b.inf(d)));
    }

    /// b ≤ c ==> a ⊓ b ≤ a ⊓ c
    proof fn lemma_inf_le_inf_left(a: Self, b: Self, c: Self)
        requires
            b.le(c),
        ensures
            a.inf(b).le(a.inf(c)),
    {
        Self::lemma_le_refl();
        Self::lemma_inf_le_inf(a, a, b, c);
    }

    /// b <= c ==> b ⊓ a <= c ⊓ a
    proof fn lemma_inf_le_inf_right(a: Self, b: Self, c: Self)
        requires
            b.le(c),
        ensures
            b.inf(a).le(c.inf(a)),
    {
        Self::lemma_le_refl();
        Self::lemma_inf_le_inf(b, c, a, a);
        assert(a.le(a));
        assert(b.inf(a).le(c.inf(a)));
    }

    /// a ⊓ a == a
    proof fn lemma_inf_idem(a: Self)
        ensures
            a.inf(a) == a,
    {
        Self::lemma_inf_eq_left(a, a);
        Self::lemma_le_refl();
    }

    /// a ⊓ b == b ⊓ a
    proof fn lemma_inf_comm(a: Self, b: Self)
        ensures
            a.inf(b) == b.inf(a),
    {
        Self::lemma_le_antisymm();
        Self::lemma_le_inf_iff(a.inf(b), b, a);
        Self::lemma_le_inf_iff(b.inf(a), a, b);
        Self::lemma_inf_le_left();
        Self::lemma_inf_le_right();
    }

    /// a ⊓ b ⊓ c == a ⊓ (b ⊓ c)
    proof fn lemma_inf_assoc(a: Self, b: Self, c: Self)
        ensures
            a.inf(b).inf(c) == a.inf(b.inf(c)),
    {
        Self::lemma_le_antisymm();
        Self::lemma_le_inf();
        Self::lemma_inf_le_left();
        Self::lemma_inf_le_right();
        Self::lemma_le_trans();

        assert(a.inf(b).inf(c) == a.inf(b.inf(c))) by {
            let lhs = a.inf(b).inf(c);
            let rhs = a.inf(b.inf(c));

            assert(lhs.le(rhs)) by {
                assert(lhs.le(a)) by {
                    assert(a.inf(b).inf(c).le(a.inf(b)));
                    assert(a.inf(b).le(a));
                };
                assert(lhs.le(b)) by {
                    assert(a.inf(b).inf(c).le(a.inf(b)));
                    assert(a.inf(b).le(b));
                };
                assert(lhs.le(c));
                assert(lhs.le(b.inf(c)));
                assert(lhs.le(a.inf(b.inf(c))));
            };

            assert(rhs.le(lhs)) by {
                assert(rhs.le(a));
                assert(rhs.le(b)) by {
                    assert(a.inf(b.inf(c)).le(b.inf(c)));
                    assert(b.inf(c).le(b));
                };
                assert(rhs.le(c)) by {
                    assert(a.inf(b.inf(c)).le(b.inf(c)));
                    assert(b.inf(c).le(c));
                };
                assert(rhs.le(a.inf(b)));
                assert(rhs.le(a.inf(b).inf(c)));
            };
        };
    }

    /// a ⊓ b ⊓ c == c ⊓ b ⊓ a
    proof fn lemma_inf_left_right_swap(a: Self, b: Self, c: Self)
        ensures
            a.inf(b).inf(c) == c.inf(b).inf(a),
    {
        Self::lemma_inf_comm(a, b);
        Self::lemma_inf_comm(a, c);
        Self::lemma_inf_comm(b, c);
        Self::lemma_inf_comm(a.inf(b), c);
        Self::lemma_inf_comm(c.inf(b), a);
        Self::lemma_inf_assoc(a, b, c);
        Self::lemma_inf_assoc(b, a, c);
        Self::lemma_inf_assoc(c, b, a);
    }

    /// a ⊓ (a ⊓ b) == a ⊓ b
    proof fn lemma_inf_left_idem(a: Self, b: Self)
        ensures
            a.inf(a.inf(b)) == a.inf(b),
    {
        Self::lemma_inf_assoc(a, a, b);
        Self::lemma_inf_idem(a);
    }

    /// a ⊓ b ⊓ b == a ⊓ b
    proof fn lemma_inf_right_idem(a: Self, b: Self)
        ensures
            a.inf(b).inf(b) == a.inf(b),
    {
        Self::lemma_inf_assoc(a, b, b);
        Self::lemma_inf_idem(b);
    }

    /// a ⊓ (b ⊓ c) == b ⊓ (a ⊓ c)
    proof fn lemma_inf_left_comm(a: Self, b: Self, c: Self)
        ensures
            a.inf(b.inf(c)) == b.inf(a.inf(c)),
    {
        Self::lemma_inf_assoc(a, b, c);
        Self::lemma_inf_assoc(b, a, c);
        Self::lemma_inf_comm(a, b);
    }

    /// a ⊓ b ⊓ c == a ⊓ c ⊓ b
    proof fn lemma_inf_right_comm(a: Self, b: Self, c: Self)
        ensures
            a.inf(b).inf(c) == a.inf(c).inf(b),
    {
        Self::lemma_inf_assoc(a, b, c);
        Self::lemma_inf_assoc(a, c, b);
        Self::lemma_inf_comm(b, c);
    }

    /// a ⊓ b ⊓ (c ⊓ d) == a ⊓ c ⊓ (b ⊓ d)
    proof fn lemma_inf_inf_inf_comm(a: Self, b: Self, c: Self, d: Self)
        ensures
            a.inf(b).inf(c.inf(d)) == a.inf(c).inf(b.inf(d)),
    {
        Self::lemma_inf_assoc(a, b, c.inf(d));
        Self::lemma_inf_assoc(a, c, b.inf(d));
        Self::lemma_inf_left_comm(b, c, d);
    }

    /// a ⊓ (b ⊓ c) == a ⊓ b ⊓ (a ⊓ c)
    proof fn lemma_inf_inf_distrib_left(a: Self, b: Self, c: Self)
        ensures
            a.inf(b.inf(c)) == a.inf(b).inf(a.inf(c)),
    {
        Self::lemma_inf_inf_inf_comm(a, b, a, c);
        Self::lemma_inf_idem(a);
    }

    /// a ⊓ b ⊓ c == a ⊓ c ⊓ (b ⊓ c)
    proof fn lemma_inf_inf_distrib_right(a: Self, b: Self, c: Self)
        ensures
            a.inf(b).inf(c) == a.inf(c).inf(b.inf(c)),
    {
        Self::lemma_inf_inf_inf_comm(a, c, b, c);
        Self::lemma_inf_idem(c);
    }

    /// a ⊓ c <= b ==> a ⊓ b <= c ==> a ⊓ b == a ⊓ c
    proof fn lemma_inf_congr_left(a: Self, b: Self, c: Self)
        requires
            a.inf(c).le(b),
            a.inf(b).le(c),
        ensures
            a.inf(b) == a.inf(c),
    {
        Self::lemma_le_antisymm();
        Self::lemma_le_inf_iff(a.inf(b), a, c);
        Self::lemma_le_inf_iff(a.inf(c), a, b);
        Self::lemma_inf_le_left();
    }

    /// b ⊓ c <= a ==> a ⊓ c <= b ==> a ⊓ c == b ⊓ c
    proof fn lemma_inf_congr_right(a: Self, b: Self, c: Self)
        requires
            b.inf(c).le(a),
            a.inf(c).le(b),
        ensures
            a.inf(c) == b.inf(c),
    {
        Self::lemma_le_antisymm();
        Self::lemma_le_inf_iff(a.inf(c), b, c);
        Self::lemma_le_inf_iff(b.inf(c), a, c);
        Self::lemma_inf_le_right();
    }

    /// a ⊓ b == a ⊓ c <==> a ⊓ c <= b ∧ a ⊓ b <= c
    proof fn lemma_inf_eq_inf_iff_left(a: Self, b: Self, c: Self)
        ensures
            (a.inf(b) == a.inf(c)) <==> (a.inf(c).le(b) && a.inf(b).le(c)),
    {
        Self::lemma_inf_le_right();

        if a.inf(c).le(b) && a.inf(b).le(c) {
            Self::lemma_inf_congr_left(a, b, c);
            assert(a.inf(b) == a.inf(c));
        }
    }

    /// a ⊓ c == b ⊓ c <==> b ⊓ c <= a ∧ a ⊓ c <= b
    proof fn lemma_inf_eq_inf_iff_right(a: Self, b: Self, c: Self)
        ensures
            (a.inf(c) == b.inf(c)) <==> (b.inf(c).le(a) && a.inf(c).le(b)),
    {
        Self::lemma_inf_le_left();

        if b.inf(c).le(a) && a.inf(c).le(b) {
            Self::lemma_inf_congr_right(a, b, c);
            assert(a.inf(c) == b.inf(c));
        }
    }

    /// a != b ==> a ⊓ b < a ∨ a ⊓ b < b
    proof fn lemma_ne_inf_lt_or_inf_lt(a: Self, b: Self)
        requires
            a != b,
        ensures
            a.inf(b).lt(a) || a.inf(b).lt(b),
    {
        Self::lemma_inf_lt_left(a, b);
        Self::lemma_inf_lt_right(a, b);
        Self::lemma_le_antisymm();
    }
}

/// Corresponds to Lean's `class Lattice (α : Type u)`.
/// A lattice is a join-semilattice which is also a meet-semilattice.
pub trait Lattice: SemilatticeSup + SemilatticeInf where Self: Sized {
    /// a ⊓ b <= a ⊔ b
    proof fn lemma_inf_le_sup(a: Self, b: Self)
        ensures
            a.inf(b).le(a.sup(b)),
    {
        Self::lemma_inf_le_left();
        Self::lemma_le_sup_left();
        Self::lemma_le_trans();

        assert(a.inf(b).le(a));
        assert(a.le(a.sup(b)));
        assert(a.inf(b).le(a.sup(b)));
    }

    /// a ⊔ b <= a ⊓ b <==> (a == b)
    proof fn lemma_sup_le_inf(a: Self, b: Self)
        ensures
            a.sup(b).le(a.inf(b)) <==> (a == b),
    {
        Self::lemma_le_sup_left();
        Self::lemma_le_sup_right();
        Self::lemma_inf_le_left();
        Self::lemma_inf_le_right();
        Self::lemma_le_trans();
        Self::lemma_le_antisymm();
        Self::lemma_sup_idem(a);
        Self::lemma_inf_idem(a);

        if a.sup(b).le(a.inf(b)) {
            assert(a.le(a.sup(b)));
            assert(a.inf(b).le(b));
            assert(a.le(b));

            assert(b.le(a.sup(b)));
            assert(a.inf(b).le(a));
            assert(b.le(a));

            assert(a == b);
        }
    }

    /// a ⊓ b == a ⊔ b <==> (a == b)
    proof fn lemma_inf_eq_sup(a: Self, b: Self)
        ensures
            (a.inf(b) == a.sup(b)) <==> (a == b),
    {
        Self::lemma_inf_le_sup(a, b);
        Self::lemma_sup_le_inf(a, b);
        Self::lemma_le_antisymm();
    }

    /// a ⊔ b == a ⊓ b <==> (a == b)
    proof fn lemma_sup_eq_inf(a: Self, b: Self)
        ensures
            (a.sup(b) == a.inf(b)) <==> (a == b),
    {
        Self::lemma_inf_eq_sup(a, b);
    }

    /// a ⊓ b < a ⊔ b <==> (a != b)
    proof fn lemma_inf_lt_sup(a: Self, b: Self)
        ensures
            a.inf(b).lt(a.sup(b)) <==> (a != b),
    {
        Self::lemma_inf_le_sup(a, b);
        Self::lemma_inf_eq_sup(a, b);
        Self::lemma_lt_iff_le_not_le();
        Self::lemma_le_antisymm();
    }

    /// a ⊓ b == c ∧ a ⊔ b == c <==> (a == c && b == c)
    proof fn lemma_inf_eq_and_sup_eq_iff(a: Self, b: Self, c: Self)
        ensures
            (a.inf(b) == c && a.sup(b) == c) <==> (a == c && b == c),
    {
        Self::lemma_sup_eq_inf(a, b);
        Self::lemma_inf_idem(a);
        Self::lemma_inf_idem(b);
        Self::lemma_inf_idem(c);
        Self::lemma_sup_idem(a);
        Self::lemma_sup_idem(b);
        Self::lemma_sup_idem(c);
    }

    /// a ⊔ (b ⊓ c) <= (a ⊔ b) ⊓ (a ⊔ c)
    proof fn lemma_sup_inf_le(a: Self, b: Self, c: Self)
        ensures
            a.sup(b.inf(c)).le(a.sup(b).inf(a.sup(c))),
    {
        Self::lemma_le_inf();
        Self::lemma_inf_le_left();
        Self::lemma_inf_le_right();
        Self::lemma_sup_le_sup_left(b.inf(c), b, a);
        Self::lemma_sup_le_sup_left(b.inf(c), c, a);

        assert(a.sup(b.inf(c)).le(a.sup(b))) by {
            assert(b.inf(c).le(b)) by {
                Self::lemma_inf_le_left();
            };
            Self::lemma_sup_le_sup_left(b.inf(c), b, a);
        };

        assert(a.sup(b.inf(c)).le(a.sup(c))) by {
            assert(b.inf(c).le(c)) by {
                Self::lemma_inf_le_right();
            };
            Self::lemma_sup_le_sup_left(b.inf(c), c, a);
        };
        assert(a.sup(b.inf(c)).le(a.sup(b).inf(a.sup(c))));
    }

    /// a ⊓ b ⊔ (a ⊓ c) <= a ⊓ (b ⊔ c)
    proof fn lemma_le_inf_sup(a: Self, b: Self, c: Self)
        ensures
            a.inf(b).sup(a.inf(c)).le(a.inf(b.sup(c))),
    {
        Self::lemma_sup_le();
        Self::lemma_le_inf();
        Self::lemma_inf_le_left();
        Self::lemma_inf_le_right();
        Self::lemma_le_sup_left();
        Self::lemma_le_sup_right();
        Self::lemma_le_trans();
        assert(a.inf(b).le(a.inf(b.sup(c)))) by {
            assert(a.inf(b).le(a));

            assert(a.inf(b).le(b.sup(c))) by {
                assert(a.inf(b).le(b));
                assert(b.le(b.sup(c)));
            };
        };

        assert(a.inf(c).le(a.inf(b.sup(c)))) by {
            assert(a.inf(c).le(a));

            assert(a.inf(c).le(b.sup(c))) by {
                assert(a.inf(c).le(c));
                assert(c.le(b.sup(c)));
            };
        };

        assert(a.inf(b).sup(a.inf(c)).le(a.inf(b.sup(c))));
    }

    /// a ⊓ (a ⊔ b) == a
    proof fn lemma_inf_sup_self(a: Self, b: Self)
        ensures
            a.inf(a.sup(b)) == a,
    {
        Self::lemma_inf_eq_left(a, a.sup(b));
        Self::lemma_le_sup_left();
    }

    /// a ⊔ (a ⊓ b) == a
    proof fn lemma_sup_inf_self(a: Self, b: Self)
        ensures
            a.sup(a.inf(b)) == a,
    {
        Self::lemma_sup_eq_left(a, a.inf(b));
        Self::lemma_inf_le_left();
    }

    /// a ⊔ b == b <==> a ⊓ b == a
    proof fn lemma_sup_eq_iff_inf_eq(a: Self, b: Self)
        ensures
            (a.sup(b) == b) <==> (a.inf(b) == a),
    {
        Self::lemma_sup_eq_right(a, b);
        Self::lemma_inf_eq_left(a, b);
    }
}

/// ### Distributive lattices
/// Corresponds to Lean's `class DistribLattice (α)`.
/// A distributive lattice is a lattice that satisfies any of four
/// equivalent distributive properties (of `sup` over `inf` or `inf` over `sup`,
/// on the left or right).
///
/// The definition here chooses `le_sup_inf`: `(x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ (y ⊓ z)`. To prove distributivity
/// from the dual law, use `DistribLattice.of_inf_sup_le`.
///
/// A classic example of a distributive lattice
/// is the lattice of subsets of a set, and in fact this example is
/// generic in the sense that every distributive lattice is realizable
/// as a sublattice of a powerset lattice.
pub trait DistribLattice: Lattice where Self: Sized {
    /// The infimum distributes over the supremum
    /// ∀ x y z : α, (x ⊔ y) ⊓ (x ⊔ z) ≤ x ⊔ y ⊓ z
    proof fn lemma_le_sup_inf()
        ensures
            forall|x: Self, y: Self, z: Self| #[trigger] x.sup(y).inf(x.sup(z)).le(x.sup(y.inf(z))),
    ;

    /// a ⊔ (b ⊓ c) == (a ⊔ b) ⊓ (a ⊔ c)
    proof fn lemma_sup_inf_left(a: Self, b: Self, c: Self)
        ensures
            a.sup(b.inf(c)) == a.sup(b).inf(a.sup(c)),
    {
        Self::lemma_le_antisymm();
        Self::lemma_le_sup_inf();
        Self::lemma_sup_inf_le(a, b, c);
        Self::lemma_le_inf();
        Self::lemma_inf_le_left();
        Self::lemma_inf_le_right();
        Self::lemma_sup_le_sup_left(b.inf(c), b, a);
        Self::lemma_sup_le_sup_left(b.inf(c), c, a);

        assert(a.sup(b.inf(c)) == a.sup(b).inf(a.sup(c))) by {
            assert(a.sup(b.inf(c)).le(a.sup(b).inf(a.sup(c)))) by {
                Self::lemma_sup_inf_le(a, b, c);
            };

            assert(a.sup(b).inf(a.sup(c)).le(a.sup(b.inf(c)))) by {
                Self::lemma_le_sup_inf();
            };
        };
    }

    /// a ⊓ b ⊔ c == (a ⊔ c) ⊓ (b ⊔ c)
    proof fn lemma_sup_inf_right(a: Self, b: Self, c: Self)
        ensures
            a.inf(b).sup(c) == a.sup(c).inf(b.sup(c)),
    {
        Self::lemma_sup_inf_left(c, a, b);
        Self::lemma_sup_comm(a.inf(b), c);
        Self::lemma_sup_comm(a, c);
        Self::lemma_sup_comm(b, c);
    }

    /// a ⊓ (b ⊔ c) == (a ⊓ b) ⊔ (a ⊓ c)
    proof fn lemma_inf_sup_left(a: Self, b: Self, c: Self)
        ensures
            a.inf(b.sup(c)) == a.inf(b).sup(a.inf(c)),
    {
        Self::lemma_le_antisymm();
        Self::lemma_sup_inf_left(a, b, c);
        Self::lemma_sup_inf_right(c, a, b);
        Self::lemma_sup_inf_self(a, b);
        Self::lemma_inf_sup_self(a, c);
        Self::lemma_sup_comm(a, c);
        Self::lemma_sup_comm(b, c);
        Self::lemma_sup_comm(a.inf(b), c);
        Self::lemma_inf_assoc(a, a.sup(c), b.sup(c));
        Self::lemma_inf_assoc(a, c.sup(a), c.sup(b));
        Self::lemma_inf_assoc(a, c, a.inf(b));

        assert(a.inf(b.sup(c)) == a.inf(a.sup(c)).inf(b.sup(c)));
        assert(a.inf(b.sup(c)) == a.inf(a.inf(b).sup(c))) by {
            Self::lemma_inf_assoc(a, a.inf(b), c);
            Self::lemma_sup_inf_right(a, b, c);
        };
        assert(a.inf(b.sup(c)) == (a.sup(a.inf(b))).inf(a.inf(b).sup(c)));
        assert(a.inf(b.sup(c)) == (a.inf(b).sup(a)).inf(a.inf(b).sup(c))) by {
            Self::lemma_sup_comm(a.inf(b), a);
        };
        assert(a.inf(b.sup(c)) == a.inf(b).sup(a.inf(c))) by {
            Self::lemma_sup_inf_left(a.inf(b), a, c);
        };

    }

    /// (a ⊔ b) ⊓ c = (a ⊓ c) ⊔ (b ⊓ c)
    proof fn lemma_inf_sup_right(a: Self, b: Self, c: Self)
        ensures
            a.sup(b).inf(c) == a.inf(c).sup(b.inf(c)),
    {
        Self::lemma_inf_sup_left(c, a, b);
        Self::lemma_inf_comm(a.sup(b), c);
        Self::lemma_inf_comm(a, c);
        Self::lemma_inf_comm(b, c);
    }

    /// x ⊓ z ≤ y ⊓ z ==> x ⊔ z ≤ y ⊔ z ==> x ≤ y
    proof fn lemma_le_of_inf_le_sup_le(x: Self, y: Self, z: Self)
        requires
            x.inf(z).le(y.inf(z)),
            x.sup(z).le(y.sup(z)),
        ensures
            x.le(y),
    {
        Self::lemma_le_trans();
        Self::lemma_le_sup_right();
        Self::lemma_sup_inf_left(x, y, z);
        Self::lemma_sup_inf_left(y, x, z);
        Self::lemma_sup_comm(x, y);
        Self::lemma_sup_inf_self(y, z);

        assert(x.le(y.inf(z).sup(x)));
        assert(y.inf(z).sup(x) == (y.sup(x)).inf(x.sup(z))) by {
            Self::lemma_sup_inf_right(y, z, x);
            Self::lemma_sup_comm(x, z);

        };
        assert((y.sup(x)).inf(x.sup(z)).le((y.sup(x)).inf(y.sup(z)))) by {
            Self::lemma_inf_le_inf_left(y.sup(x), x.sup(z), y.sup(z));
        };
        assert((y.sup(x)).inf(y.sup(z)) == y.sup(x.inf(z))) by {
            Self::lemma_sup_inf_left(y, x, z);
        };
        assert(y.sup(x.inf(z)).le(y.sup(y.inf(z)))) by {
            Self::lemma_sup_le_sup_left(x.inf(z), y.inf(z), y);
        };
        assert(y.sup(y.inf(z)).le(y)) by {
            Self::lemma_inf_le_left();
            Self::lemma_sup_le();
            Self::lemma_le_refl();
        }
    }

    /// b ⊓ a = c ⊓ a ==> b ⊔ a = c ⊔ a ==> b = c
    proof fn lemma_eq_of_inf_eq_sup_eq(a: Self, b: Self, c: Self)
        requires
            b.inf(a) == c.inf(a),
            b.sup(a) == c.sup(a),
        ensures
            b == c,
    {
        Self::lemma_le_antisymm();
        Self::lemma_le_refl();
        Self::lemma_le_of_inf_le_sup_le(b, c, a);
        Self::lemma_le_of_inf_le_sup_le(c, b, a);

        assert(b.le(c)) by {
            assert(b.inf(a).le(c.inf(a))) by {
                assert(b.inf(a).le(b.inf(a)));
            };
            assert(b.sup(a).le(c.sup(a))) by {
                assert(b.sup(a).le(b.sup(a)));
            };
            Self::lemma_le_of_inf_le_sup_le(b, c, a);
        };

        assert(c.le(b)) by {
            assert(c.inf(a) == b.inf(a));
            assert(c.inf(a).le(b.inf(a))) by {
                assert(c.inf(a).le(c.inf(a)));
            };

            assert(c.sup(a) == b.sup(a));
            assert(c.sup(a).le(b.sup(a))) by {
                assert(c.sup(a).le(c.sup(a)));
            };
            Self::lemma_le_of_inf_le_sup_le(c, b, a);
        };

        assert(b == c);
    }
}

impl<T: SemilatticeSup> Max for T {
    open spec fn max(self, rhs: Self) -> Self {
        self.sup(rhs)
    }
}

impl<T: SemilatticeInf> Min for T {
    open spec fn min(self, rhs: Self) -> Self {
        self.inf(rhs)
    }
}

} // verus!
