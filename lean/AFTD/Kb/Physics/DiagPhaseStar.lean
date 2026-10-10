import AFTD.Prelude
import AFTD.Kb.Physics.DiagPhase
import AFTD.Kb.Physics.DiagPhaseZero
import AFTD.Kb.Physics.DiagPhaseZeroEq

/-!
# diagPhase_star

Topic: quantum_field_theory   Node: 5e256c174984

Provenance: formalization of a published result. Source: Physlib, `diagPhase_star`. Lean proof by Prabhoda Chandra Sarjapur, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/NeutrinoPhysics/Basic.lean (Copyright (c) 2025 Prabhoda Chandra Sarjapur. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

lemma stating that the Hermitian conjugate of diagPhase diag(+iθ_i) is just diagPhase with entries diag(-iθ_i)
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix Complex in
/-- lemma stating that the Hermitian conjugate of diagPhase diag(+iθ_i) is just diagPhase with entries diag(-iθ_i) -/
@[simp]
lemma diagPhase_star (θ : Fin 3 → ℝ) :
    (diagPhase θ)ᴴ = diagPhase (- θ) := by
    show (Matrix.diagonal _)ᴴ = Matrix.diagonal _
    simp [Matrix.diagonal_conjTranspose, ← exp_conj]
