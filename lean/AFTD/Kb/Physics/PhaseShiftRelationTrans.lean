import AFTD.Prelude
import AFTD.Kb.Physics.PhaseShiftRelation
import AFTD.Kb.Physics.PhaseShift
import AFTD.Kb.Physics.PhaseShiftMatrix
import AFTD.Kb.Physics.PhaseShiftMatrixMul
import AFTD.Kb.Physics.PhaseShiftCoeMatrix
import AFTD.Kb.Tcs.OrthInterEqOrthSubImage

/-!
# phaseShiftRelation_trans

Topic: quantum_field_theory   Node: 1711b1393ff5

Provenance: formalization of a published result. Source: Physlib, `phaseShiftRelation_trans`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/FlavorPhysics/CKMMatrix/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The relation `PhaseShiftRelation` is transitive.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix Complex in
/-- The relation `PhaseShiftRelation` is transitive. -/
lemma phaseShiftRelation_trans {U V W : unitaryGroup (Fin 3) ℂ} :
    PhaseShiftRelation U V → PhaseShiftRelation V W → PhaseShiftRelation U W := by
  rintro ⟨a, b, c, e, f, g, rfl⟩ ⟨d, i, j, k, l, m, rfl⟩
  refine ⟨a + d, b + i, c + j, e + k, f + l, g + m, ?_⟩
  simp only [Subtype.ext_iff, Submonoid.coe_mul, phaseShift_coe_matrix]
  rw [mul_assoc, mul_assoc, phaseShiftMatrix_mul, ← mul_assoc, ← mul_assoc, phaseShiftMatrix_mul,
    add_comm k e, add_comm l f, add_comm m g]
