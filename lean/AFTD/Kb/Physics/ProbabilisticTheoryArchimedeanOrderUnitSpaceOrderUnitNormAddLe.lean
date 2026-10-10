import AFTD.Prelude
import AFTD.Kb.Physics.ProbabilisticTheoryArchimedeanOrderUnitSpace
import AFTD.Kb.Physics.ProbabilisticTheoryArchimedeanOrderUnitSpaceOrderUnitNorm
import AFTD.Kb.Physics.ProbabilisticTheoryOrderedVectorSpace
import AFTD.Kb.Physics.ProbabilisticTheoryOrderUnitSpace
import AFTD.Kb.Physics.ProbabilisticTheoryArchimedeanOrderUnitSpaceOrderUnitBounds
import AFTD.Kb.Physics.ProbabilisticTheoryArchimedeanOrderUnitSpaceExistsOrderUnitBoundLt
import AFTD.Kb.Physics.ProbabilisticTheoryArchimedeanOrderUnitSpaceOrderUnitNormLe
import AFTD.Kb.Physics.ProbabilisticTheoryArchimedeanOrderUnitSpaceAddMemOrderUnitBounds
import AFTD.Kb.Physics.ProbabilisticTheoryArchimedeanOrderUnitSpaceOrderUnitNormZero
import AFTD.Kb.Physics.ProbabilisticTheoryArchimedeanOrderUnitSpaceOrderUnitNormNeg
import AFTD.Kb.Physics.ProbabilisticTheoryInstArchimedeanOrderUnitSpaceReal

/-!
# ProbabilisticTheory.ArchimedeanOrderUnitSpace.orderUnitNorm_add_le

Topic: quantum_mechanics   Node: 2a71646fd0f3

Provenance: formalization of a published result. Source: Physlib, `ProbabilisticTheory.ArchimedeanOrderUnitSpace.orderUnitNorm_add_le`. Lean proof by Tom Ole Diem, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ProbabilisticTheory/OrderUnit/Archimedean.lean (Copyright (c) 2026 Tom Ole Diem. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

ProbabilisticTheory.ArchimedeanOrderUnitSpace.orderUnitNorm_add_le
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ProbabilisticTheory ProbabilisticTheory.ArchimedeanOrderUnitSpace in
open ProbabilisticTheory.OrderUnitSpace in
variable {E : Type*} [ArchimedeanOrderUnitSpace E] in
lemma ProbabilisticTheory.ArchimedeanOrderUnitSpace.orderUnitNorm_add_le (A B : E) :
    orderUnitNorm (A + B) ≤ orderUnitNorm A + orderUnitNorm B := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨r, hr, hrlt⟩ := exists_orderUnitBound_lt A (half_pos hε)
  obtain ⟨s, hs, hslt⟩ := exists_orderUnitBound_lt B (half_pos hε)
  calc
    orderUnitNorm (A + B) ≤ r + s := orderUnitNorm_le (add_mem_orderUnitBounds hr hs)
    _ ≤ (orderUnitNorm A + ε / 2) + (orderUnitNorm B + ε / 2) :=
      add_le_add hrlt.le hslt.le
    _ = orderUnitNorm A + orderUnitNorm B + ε := by ring
