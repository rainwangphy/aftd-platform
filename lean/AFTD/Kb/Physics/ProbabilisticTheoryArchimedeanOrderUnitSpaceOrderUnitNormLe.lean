import AFTD.Prelude
import AFTD.Kb.Physics.ProbabilisticTheoryOrderUnitSpace
import AFTD.Kb.Physics.ProbabilisticTheoryArchimedeanOrderUnitSpaceOrderUnitBounds
import AFTD.Kb.Physics.ProbabilisticTheoryArchimedeanOrderUnitSpaceOrderUnitNorm
import AFTD.Kb.Physics.ProbabilisticTheoryArchimedeanOrderUnitSpaceOrderUnitBoundsBddBelow
import AFTD.Kb.Physics.ProbabilisticTheoryArchimedeanOrderUnitSpace
import AFTD.Kb.Physics.ProbabilisticTheoryInstArchimedeanOrderUnitSpaceReal

/-!
# ProbabilisticTheory.ArchimedeanOrderUnitSpace.orderUnitNorm_le

Topic: quantum_mechanics   Node: 13d24ec09768

Provenance: formalization of a published result. Source: Physlib, `ProbabilisticTheory.ArchimedeanOrderUnitSpace.orderUnitNorm_le`. Lean proof by Tom Ole Diem, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ProbabilisticTheory/OrderUnit/Archimedean.lean (Copyright (c) 2026 Tom Ole Diem. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Any order-unit bound on `A` is an upper bound for `A`'s order-unit norm.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ProbabilisticTheory ProbabilisticTheory.ArchimedeanOrderUnitSpace in
variable {E : Type*} [OrderUnitSpace E] in
/-- Any order-unit bound on `A` is an upper bound for `A`'s order-unit norm. -/
lemma ProbabilisticTheory.ArchimedeanOrderUnitSpace.orderUnitNorm_le {A : E} {r : ℝ} (hr : r ∈ orderUnitBounds A) :
    orderUnitNorm A ≤ r :=
  csInf_le (orderUnitBounds_bddBelow A) hr
