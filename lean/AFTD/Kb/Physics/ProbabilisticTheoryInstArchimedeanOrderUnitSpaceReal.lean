import AFTD.Prelude
import AFTD.Kb.Physics.ProbabilisticTheoryArchimedeanOrderUnitSpace
import AFTD.Kb.Physics.ProbabilisticTheoryOrderUnitSpace
import AFTD.Kb.Physics.ProbabilisticTheoryOrderedVectorSpace

/-!
# ProbabilisticTheory.instArchimedeanOrderUnitSpaceReal

Topic: quantum_mechanics   Node: 90d2cd69ef07

Provenance: formalization of a published result. Source: Physlib, `ProbabilisticTheory.instArchimedeanOrderUnitSpaceReal`. Lean proof by Tom Ole Diem, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ProbabilisticTheory/OrderUnit/Archimedean.lean (Copyright (c) 2026 Tom Ole Diem. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The real numbers form an Archimedean order-unit space.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The real numbers form an Archimedean order-unit space. -/
instance ProbabilisticTheory.instArchimedeanOrderUnitSpaceReal : ArchimedeanOrderUnitSpace ℝ where
  one_nonneg := zero_le_one
  exists_nsmul_one_le A := by
    obtain ⟨n, hn⟩ := exists_nat_ge A
    exact ⟨n, by simpa using hn⟩
  le_zero_of_forall_pos_smul_one_le A hA := by
    by_contra h
    have := hA (A / 2) (by positivity [lt_of_not_ge h])
    rw [smul_eq_mul, mul_one] at this
    linarith
