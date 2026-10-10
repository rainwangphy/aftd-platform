import AFTD.Prelude
import AFTD.Kb.Physics.CKMMatrix
import AFTD.Kb.Physics.CKMMatrixSetoid
import AFTD.Kb.Physics.VAbs'
import AFTD.Kb.Physics.PhaseShift
import AFTD.Kb.Physics.PhaseShiftMatrix
import AFTD.Kb.Physics.PhaseShiftCoeMatrix

/-!
# VAbs'_equiv

Topic: quantum_field_theory   Node: d231735afebc

Provenance: formalization of a published result. Source: Physlib, `VAbs'_equiv`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/FlavorPhysics/CKMMatrix/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If two CKM matrices are equivalent (under phase shifts), then their absolute values are the same.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix Complex in
set_option backward.isDefEq.respectTransparency false in
/-- If two CKM matrices are equivalent (under phase shifts), then their absolute values are the same. -/
lemma VAbs'_equiv (i j : Fin 3) (V U : CKMMatrix) (h : V ≈ U) :
    VAbs' V i j = VAbs' U i j := by
  obtain ⟨a, b, c, e, f, g, rfl⟩ := h
  simp only [VAbs', Submonoid.coe_mul, phaseShift_coe_matrix, phaseShiftMatrix, mul_apply,
    Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;>
    simp [Complex.norm_exp, mul_comm]
