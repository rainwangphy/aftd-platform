import AFTD.Prelude
import AFTD.Kb.Physics.PhaseShiftRelation
import AFTD.Kb.Physics.PhaseShift
import AFTD.Kb.Physics.PhaseShiftMatrix
import AFTD.Kb.Physics.PhaseShiftMatrixMul
import AFTD.Kb.Physics.PhaseShiftMatrixOne
import AFTD.Kb.Physics.PhaseShiftCoeMatrix
import AFTD.Kb.Tcs.OrthInterEqOrthSubImage
import AFTD.Kb.Tcs.BoolFourierFourierCoeffConvolution

/-!
# phaseShiftRelation_symm

Topic: quantum_field_theory   Node: fa5a727138d6

Provenance: formalization of a published result. Source: Physlib, `phaseShiftRelation_symm`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/FlavorPhysics/CKMMatrix/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The relation `PhaseShiftRelation` is symmetric.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix Complex in
/-- The relation `PhaseShiftRelation` is symmetric. -/
lemma phaseShiftRelation_symm {U V : unitaryGroup (Fin 3) ℂ} :
    PhaseShiftRelation U V → PhaseShiftRelation V U := by
  rintro ⟨a, b, c, e, f, g, rfl⟩
  refine ⟨-a, -b, -c, -e, -f, -g, ?_⟩
  simp only [Subtype.ext_iff, Submonoid.coe_mul, phaseShift_coe_matrix, mul_assoc,
    phaseShiftMatrix_mul, add_neg_cancel, phaseShiftMatrix_one, mul_one]
  simp only [← mul_assoc, phaseShiftMatrix_mul, neg_add_cancel, phaseShiftMatrix_one, one_mul]
