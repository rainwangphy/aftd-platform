import AFTD.Prelude
import AFTD.Kb.Physics.ProbabilisticTheoryOrderUnitSpace
import AFTD.Kb.Physics.ProbabilisticTheoryArchimedeanOrderUnitSpaceOrderUnitBounds
import AFTD.Kb.Physics.ProbabilisticTheoryOrderedVectorSpace
import AFTD.Kb.Physics.ProbabilisticTheoryArchimedeanOrderUnitSpace
import AFTD.Kb.Physics.ProbabilisticTheoryArchimedeanOrderUnitSpaceOrderUnitNormZero
import AFTD.Kb.Physics.ProbabilisticTheoryInstArchimedeanOrderUnitSpaceReal

/-!
# ProbabilisticTheory.ArchimedeanOrderUnitSpace.orderUnitBounds_neg

Topic: quantum_mechanics   Node: d9cc826f0682

Provenance: formalization of a published result. Source: Physlib, `ProbabilisticTheory.ArchimedeanOrderUnitSpace.orderUnitBounds_neg`. Lean proof by Tom Ole Diem, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ProbabilisticTheory/OrderUnit/Archimedean.lean (Copyright (c) 2026 Tom Ole Diem. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Negation preserves the set of order-unit bounds: a symmetric interval bounding `A` bounds `-A` too.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ProbabilisticTheory ProbabilisticTheory.ArchimedeanOrderUnitSpace in
variable {E : Type*} [OrderUnitSpace E] in
/-- Negation preserves the set of order-unit bounds: a symmetric interval bounding `A` bounds `-A` too. -/
lemma ProbabilisticTheory.ArchimedeanOrderUnitSpace.orderUnitBounds_neg (A : E) : orderUnitBounds (-A) = orderUnitBounds A := by
  ext r
  constructor <;> rintro ⟨hr, hl, hu⟩ <;>
    exact ⟨hr, by simpa only [neg_neg] using neg_le_neg hu,
      by simpa only [neg_smul, neg_neg] using neg_le_neg hl⟩
