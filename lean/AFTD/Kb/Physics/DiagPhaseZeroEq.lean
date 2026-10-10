import AFTD.Prelude
import AFTD.Kb.Physics.DiagPhase
import AFTD.Kb.Physics.DiagPhaseZero

/-!
# diagPhase_zero_eq

Topic: quantum_field_theory   Node: 709da8e4da23

Provenance: formalization of a published result. Source: Physlib, `diagPhase_zero_eq`. Lean proof by Prabhoda Chandra Sarjapur, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/NeutrinoPhysics/Basic.lean (Copyright (c) 2025 Prabhoda Chandra Sarjapur. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

lemma stating that diagPhase with θ = 0 is equal to diagPhase with all zero phases
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix Complex in
/-- lemma stating that diagPhase with θ = 0 is equal to diagPhase with all zero phases -/
@[simp]
lemma diagPhase_zero_eq : diagPhase 0 = diagPhase (fun _ : Fin 3 => 0) := by
    ext i j
    simp
