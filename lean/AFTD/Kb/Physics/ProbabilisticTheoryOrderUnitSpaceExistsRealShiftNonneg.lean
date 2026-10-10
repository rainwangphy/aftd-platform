import AFTD.Prelude
import AFTD.Kb.Physics.ProbabilisticTheoryOrderUnitSpace
import AFTD.Kb.Physics.ProbabilisticTheoryOrderedVectorSpace

/-!
# ProbabilisticTheory.OrderUnitSpace.exists_real_shift_nonneg

Topic: quantum_mechanics   Node: dc407536dcf2

Provenance: formalization of a published result. Source: Physlib, `ProbabilisticTheory.OrderUnitSpace.exists_real_shift_nonneg`. Lean proof by Tom Ole Diem, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ProbabilisticTheory/OrderUnit/Basic.lean (Copyright (c) 2026 Tom Ole Diem. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Every element becomes nonnegative after adding enough copies of the order unit: the positive cone reaches everywhere, once you're allowed to shift by the unit.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ProbabilisticTheory in
variable {E : Type*} [OrderUnitSpace E] in
/-- Every element becomes nonnegative after adding enough copies of the order unit: the positive cone reaches everywhere, once you're allowed to shift by the unit. -/
lemma ProbabilisticTheory.OrderUnitSpace.exists_real_shift_nonneg (A : E) : ∃ r : ℝ, 0 ≤ r • (1 : E) + A := by
  obtain ⟨n, hn⟩ := exists_nsmul_one_le (-A)
  use n
  rw [← sub_neg_eq_add, sub_nonneg]
  exact_mod_cast hn
