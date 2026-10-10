import AFTD.Prelude
import AFTD.Kb.Physics.ProbabilisticTheoryOrderUnitSpace
import AFTD.Kb.Physics.ProbabilisticTheoryOrderedVectorSpace

/-!
# ProbabilisticTheory.ArchimedeanOrderUnitSpace.orderUnitBounds

Topic: quantum_mechanics   Node: 99522daf482a

Provenance: formalization of a published result. Source: Physlib, `ProbabilisticTheory.ArchimedeanOrderUnitSpace.orderUnitBounds`. Lean proof by Tom Ole Diem, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ProbabilisticTheory/OrderUnit/Archimedean.lean (Copyright (c) 2026 Tom Ole Diem. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The nonnegative scalars that bound an element on both sides by the order unit.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ProbabilisticTheory in
variable {E : Type*} [OrderUnitSpace E] in
/-- The nonnegative scalars that bound an element on both sides by the order unit. -/
def ProbabilisticTheory.ArchimedeanOrderUnitSpace.orderUnitBounds (A : E) : Set ℝ :=
  {r | 0 ≤ r ∧ -(r • (1 : E)) ≤ A ∧ A ≤ r • (1 : E)}
