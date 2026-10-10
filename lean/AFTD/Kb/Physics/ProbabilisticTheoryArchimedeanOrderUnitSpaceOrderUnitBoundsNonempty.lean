import AFTD.Prelude
import AFTD.Kb.Physics.ProbabilisticTheoryOrderUnitSpace
import AFTD.Kb.Physics.ProbabilisticTheoryArchimedeanOrderUnitSpaceOrderUnitBounds
import AFTD.Kb.Physics.ProbabilisticTheoryOrderedVectorSpace
import AFTD.Kb.Physics.ProbabilisticTheoryOrderUnitSpaceExistsTwoSidedBound
import AFTD.Kb.Physics.ProbabilisticTheoryArchimedeanOrderUnitSpace
import AFTD.Kb.Physics.ProbabilisticTheoryInstArchimedeanOrderUnitSpaceReal

/-!
# ProbabilisticTheory.ArchimedeanOrderUnitSpace.orderUnitBounds_nonempty

Topic: quantum_mechanics   Node: 0566989fcb7b

Provenance: formalization of a published result. Source: Physlib, `ProbabilisticTheory.ArchimedeanOrderUnitSpace.orderUnitBounds_nonempty`. Lean proof by Tom Ole Diem, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ProbabilisticTheory/OrderUnit/Archimedean.lean (Copyright (c) 2026 Tom Ole Diem. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Every element has some order-unit bound.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ProbabilisticTheory ProbabilisticTheory.ArchimedeanOrderUnitSpace in
open ProbabilisticTheory.OrderUnitSpace in
variable {E : Type*} [OrderUnitSpace E] in
/-- Every element has some order-unit bound. -/
lemma ProbabilisticTheory.ArchimedeanOrderUnitSpace.orderUnitBounds_nonempty (A : E) : (orderUnitBounds A).Nonempty := by
  obtain ⟨n, hl, hu⟩ := exists_two_sided_bound A
  refine ⟨n, Nat.cast_nonneg n, ?_, ?_⟩
  · simpa only [Nat.cast_smul_eq_nsmul] using hl
  · simpa only [Nat.cast_smul_eq_nsmul] using hu
