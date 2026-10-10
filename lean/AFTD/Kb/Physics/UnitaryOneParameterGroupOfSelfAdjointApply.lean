import AFTD.Prelude
import AFTD.Kb.Physics.UnitaryOneParameterGroupInstCoeFunForallRealContinuousLinearMapComplexId
import AFTD.Kb.Physics.UnitaryOneParameterGroup
import AFTD.Kb.Physics.UnitaryOneParameterGroupOfSelfAdjoint
import AFTD.Kb.Physics.UnitaryOneParameterGroupGenerator
import AFTD.Kb.Physics.UnitaryOneParameterGroupAdjointEq

/-!
# UnitaryOneParameterGroup.ofSelfAdjoint_apply

Topic: classical_mechanics   Node: b104b9028166

Provenance: formalization of a published result. Source: Physlib, `UnitaryOneParameterGroup.ofSelfAdjoint_apply`. Lean proof by Tom Ole Diem, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/OneParameterSubgroups/Unitary.lean (Copyright (c) 2026 Tom Ole Diem. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

UnitaryOneParameterGroup.ofSelfAdjoint_apply
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open UnitaryOneParameterGroup in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] in
@[simp]
lemma UnitaryOneParameterGroup.ofSelfAdjoint_apply {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) (t : ℝ) :
    ofSelfAdjoint hA t = NormedSpace.exp ((-(t : ℂ) * Complex.I) • A) := by
  simp only [ofSelfAdjoint]
  change NormedSpace.exp ((t : ℂ) • ((-Complex.I) • A)) = _
  rw [smul_smul]
  ring_nf
