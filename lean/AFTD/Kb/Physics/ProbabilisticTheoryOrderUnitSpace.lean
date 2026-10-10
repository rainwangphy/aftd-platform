import AFTD.Prelude
import AFTD.Kb.Physics.ProbabilisticTheoryOrderedVectorSpace

/-!
# ProbabilisticTheory.OrderUnitSpace

Topic: quantum_mechanics   Node: ac4ea55a4fdf

Provenance: formalization of a published result. Source: Physlib, `ProbabilisticTheory.OrderUnitSpace`. Lean proof by Tom Ole Diem, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ProbabilisticTheory/OrderUnit/Basic.lean (Copyright (c) 2026 Tom Ole Diem. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An ordered real vector space whose distinguished element `1` is an order unit: it is nonnegative, and every element is bounded above by a natural multiple of it. No multiplication is assumed.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- An ordered real vector space whose distinguished element `1` is an order unit: it is nonnegative, and every element is bounded above by a natural multiple of it. No multiplication is assumed. -/
class ProbabilisticTheory.OrderUnitSpace (E : Type*) extends OrderedVectorSpace E, One E where
  /-- The distinguished unit is nonnegative. -/
  one_nonneg : 0 ≤ (1 : E)
  /-- Every element is bounded above by a natural multiple of the order unit. -/
  exists_nsmul_one_le : ∀ B : E, ∃ n : ℕ, B ≤ n • (1 : E)
