import AFTD.Prelude
import AFTD.Kb.Physics.ProbabilisticTheoryOrderUnitSpace
import AFTD.Kb.Physics.ProbabilisticTheoryArchimedeanOrderUnitSpaceOrderUnitNorm
import AFTD.Kb.Physics.ProbabilisticTheoryArchimedeanOrderUnitSpaceOrderUnitBounds
import AFTD.Kb.Physics.ProbabilisticTheoryArchimedeanOrderUnitSpaceOrderUnitBoundsNonempty
import AFTD.Kb.Physics.ProbabilisticTheoryOrderedVectorSpace
import AFTD.Kb.Physics.ProbabilisticTheoryArchimedeanOrderUnitSpace
import AFTD.Kb.Physics.ProbabilisticTheoryInstArchimedeanOrderUnitSpaceReal

/-!
# ProbabilisticTheory.ArchimedeanOrderUnitSpace.orderUnitNorm_nonneg

Topic: quantum_mechanics   Node: 198fab691b3e

Provenance: formalization of a published result. Source: Physlib, `ProbabilisticTheory.ArchimedeanOrderUnitSpace.orderUnitNorm_nonneg`. Lean proof by Tom Ole Diem, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ProbabilisticTheory/OrderUnit/Archimedean.lean (Copyright (c) 2026 Tom Ole Diem. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The order-unit norm is an infimum of nonnegative reals, hence itself nonnegative.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ProbabilisticTheory ProbabilisticTheory.ArchimedeanOrderUnitSpace in
open ProbabilisticTheory.OrderUnitSpace in
variable {E : Type*} [OrderUnitSpace E] in
/-- The order-unit norm is an infimum of nonnegative reals, hence itself nonnegative. -/
lemma ProbabilisticTheory.ArchimedeanOrderUnitSpace.orderUnitNorm_nonneg (A : E) : 0 ≤ orderUnitNorm A :=
  le_csInf (orderUnitBounds_nonempty A) fun _ hr ↦ hr.1
