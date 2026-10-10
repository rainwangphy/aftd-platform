import AFTD.Prelude
import AFTD.Kb.Physics.PhaseShiftRelation
import AFTD.Kb.Physics.PhaseShift
import AFTD.Kb.Physics.PhaseShiftMatrixOne
import AFTD.Kb.Physics.PhaseShiftCoeMatrix
import AFTD.Kb.Physics.PhaseShiftMatrix
import AFTD.Kb.Tcs.OrthInterEqOrthSubImage

/-!
# phaseShiftRelation_refl

Topic: quantum_field_theory   Node: 04f2dbab0ad7

Provenance: formalization of a published result. Source: Physlib, `phaseShiftRelation_refl`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/FlavorPhysics/CKMMatrix/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The relation `PhaseShiftRelation` is reflective.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix Complex in
/-- The relation `PhaseShiftRelation` is reflective. -/
lemma phaseShiftRelation_refl (U : unitaryGroup (Fin 3) ℂ) : PhaseShiftRelation U U := by
  refine ⟨0, 0, 0, 0, 0, 0, ?_⟩
  simp only [Subtype.ext_iff, Submonoid.coe_mul, phaseShift_coe_matrix, phaseShiftMatrix_one,
    one_mul, mul_one]
