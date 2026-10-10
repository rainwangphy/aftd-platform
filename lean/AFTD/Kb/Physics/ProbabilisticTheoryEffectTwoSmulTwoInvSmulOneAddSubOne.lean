import AFTD.Prelude
import AFTD.Kb.Physics.ProbabilisticTheoryArchimedeanOrderUnitSpace
import AFTD.Kb.Physics.ProbabilisticTheoryOrderedVectorSpace
import AFTD.Kb.Physics.ProbabilisticTheoryOrderUnitSpace
import AFTD.Kb.Physics.ProbabilisticTheoryArchimedeanOrderUnitSpaceOrderUnitNormZero
import AFTD.Kb.Physics.ProbabilisticTheoryArchimedeanOrderUnitSpaceOrderUnitNormNeg
import AFTD.Kb.Physics.ProbabilisticTheoryInstArchimedeanOrderUnitSpaceReal

/-!
# ProbabilisticTheory.Effect.two_smul_two_inv_smul_one_add_sub_one

Topic: quantum_mechanics   Node: 7d2b76b3169d

Provenance: formalization of a published result. Source: Physlib, `ProbabilisticTheory.Effect.two_smul_two_inv_smul_one_add_sub_one`. Lean proof by Tom Ole Diem, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ProbabilisticTheory/Effect/Metric.lean (Copyright (c) 2026 Tom Ole Diem. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Undoing the re-centering, then redoing it, returns the original ball point.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ProbabilisticTheory in
variable {E : Type*} [ArchimedeanOrderUnitSpace E] in
/-- Undoing the re-centering, then redoing it, returns the original ball point. -/
lemma ProbabilisticTheory.Effect.two_smul_two_inv_smul_one_add_sub_one (A : E) :
    2 • ((2 : ℝ)⁻¹ • (1 + A)) - 1 = A := by
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  norm_num
