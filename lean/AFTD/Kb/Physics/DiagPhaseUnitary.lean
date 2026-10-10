import AFTD.Prelude
import AFTD.Kb.Physics.DiagPhase
import AFTD.Kb.Physics.DiagPhaseStar
import AFTD.Kb.Physics.DiagPhaseZero
import AFTD.Kb.Physics.DiagPhaseZeroEq
import AFTD.Kb.Physics.DiagPhaseMul

/-!
# diagPhaseUnitary

Topic: quantum_field_theory   Node: 71eafd076515

Provenance: formalization of a published result. Source: Physlib, `diagPhaseUnitary`. Lean proof by Prabhoda Chandra Sarjapur, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/NeutrinoPhysics/Basic.lean (Copyright (c) 2025 Prabhoda Chandra Sarjapur. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

diagonal phase matrix diag(iθ_i) is part of the unitary group
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix Complex in
/-- diagonal phase matrix diag(iθ_i) is part of the unitary group -/
noncomputable def diagPhaseUnitary (θ : Fin 3 → ℝ) : unitaryGroup (Fin 3) ℂ :=
    ⟨diagPhase θ,
    by
    rw[Matrix.mem_unitaryGroup_iff]
    change _ * (diagPhase θ)ᴴ = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diagPhase,
    Matrix.mul_apply,
    ← exp_add]⟩
