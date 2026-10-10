import AFTD.Prelude
import AFTD.Kb.Physics.ProbabilisticTheoryOrderUnitSpace
import AFTD.Kb.Physics.ProbabilisticTheoryOrderedVectorSpace

/-!
# ProbabilisticTheory.OrderUnitSpace.exists_eq_sub_nonneg

Topic: quantum_mechanics   Node: c91e3bde201d

Provenance: formalization of a published result. Source: Physlib, `ProbabilisticTheory.OrderUnitSpace.exists_eq_sub_nonneg`. Lean proof by Tom Ole Diem, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ProbabilisticTheory/OrderUnit/Basic.lean (Copyright (c) 2026 Tom Ole Diem. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Every element is a difference of two positive elements.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ProbabilisticTheory in
variable {E : Type*} [OrderUnitSpace E] in
/-- Every element is a difference of two positive elements. -/
lemma ProbabilisticTheory.OrderUnitSpace.exists_eq_sub_nonneg (A : E) : ∃ Ap An : E, 0 ≤ Ap ∧ 0 ≤ An ∧ A = Ap - An := by
  obtain ⟨n, hn⟩ := exists_nsmul_one_le (-A)
  refine ⟨A + n • (1 : E), n • (1 : E), ?_, nsmul_nonneg one_nonneg n, ?_⟩
  · exact neg_le_iff_add_nonneg'.mp hn
  · exact (add_sub_cancel_right A (n • (1 : E))).symm
