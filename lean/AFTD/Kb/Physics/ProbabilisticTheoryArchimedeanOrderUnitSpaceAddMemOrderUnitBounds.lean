import AFTD.Prelude
import AFTD.Kb.Physics.ProbabilisticTheoryOrderUnitSpace
import AFTD.Kb.Physics.ProbabilisticTheoryArchimedeanOrderUnitSpaceOrderUnitBounds
import AFTD.Kb.Physics.ProbabilisticTheoryOrderedVectorSpace
import AFTD.Kb.Physics.ProbabilisticTheoryArchimedeanOrderUnitSpace
import AFTD.Kb.Physics.ProbabilisticTheoryArchimedeanOrderUnitSpaceOrderUnitNormZero
import AFTD.Kb.Physics.ProbabilisticTheoryArchimedeanOrderUnitSpaceOrderUnitNormNeg
import AFTD.Kb.Physics.ProbabilisticTheoryInstArchimedeanOrderUnitSpaceReal

/-!
# ProbabilisticTheory.ArchimedeanOrderUnitSpace.add_mem_orderUnitBounds

Topic: quantum_mechanics   Node: 190461cbe9fb

Provenance: formalization of a published result. Source: Physlib, `ProbabilisticTheory.ArchimedeanOrderUnitSpace.add_mem_orderUnitBounds`. Lean proof by Tom Ole Diem, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ProbabilisticTheory/OrderUnit/Archimedean.lean (Copyright (c) 2026 Tom Ole Diem. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A bound for `A` and a bound for `B` add up to a bound for `A + B`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ProbabilisticTheory ProbabilisticTheory.ArchimedeanOrderUnitSpace in
variable {E : Type*} [OrderUnitSpace E] in
/-- A bound for `A` and a bound for `B` add up to a bound for `A + B`. -/
lemma ProbabilisticTheory.ArchimedeanOrderUnitSpace.add_mem_orderUnitBounds {A B : E} {r s : ℝ} (hr : r ∈ orderUnitBounds A)
    (hs : s ∈ orderUnitBounds B) : r + s ∈ orderUnitBounds (A + B) := by
  refine ⟨add_nonneg hr.1 hs.1, ?_, ?_⟩
  · rw [add_smul, neg_add]
    exact add_le_add hr.2.1 hs.2.1
  · rw [add_smul]
    exact add_le_add hr.2.2 hs.2.2
