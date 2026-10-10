import AFTD.Prelude
import AFTD.Kb.Physics.ProbabilisticTheoryOrderUnitSpace
import AFTD.Kb.Physics.ProbabilisticTheoryOrderedVectorSpace

/-!
# ProbabilisticTheory.ArchimedeanOrderUnitSpace

Topic: quantum_mechanics   Node: 053fd69f3314

Provenance: formalization of a published result. Source: Physlib, `ProbabilisticTheory.ArchimedeanOrderUnitSpace`. Lean proof by Tom Ole Diem, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ProbabilisticTheory/OrderUnit/Archimedean.lean (Copyright (c) 2026 Tom Ole Diem. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An order-unit space whose distinguished order unit is Archimedean.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- An order-unit space whose distinguished order unit is Archimedean. -/
class ProbabilisticTheory.ArchimedeanOrderUnitSpace (E : Type*) extends OrderUnitSpace E where
  /-- If `A` is smaller than every positive multiple of `1`, `A` is already `≤ 0`. -/
  le_zero_of_forall_pos_smul_one_le : ∀ A : E, (∀ ε : ℝ, 0 < ε → A ≤ ε • (1 : E)) → A ≤ 0
