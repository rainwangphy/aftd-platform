import AFTD.Prelude
import AFTD.Kb.Physics.DiagPhase

/-!
# diagPhase_zero

Topic: quantum_field_theory   Node: 40f3e67bc418

Provenance: formalization of a published result. Source: Physlib, `diagPhase_zero`. Lean proof by Prabhoda Chandra Sarjapur, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/NeutrinoPhysics/Basic.lean (Copyright (c) 2025 Prabhoda Chandra Sarjapur. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

lemma stating that the diagonal phase matrix with all zeros is the identity matrix
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix Complex in
/-- lemma stating that the diagonal phase matrix with all zeros is the identity matrix -/
@[simp]
lemma diagPhase_zero:
    diagPhase (fun _ : Fin 3 => 0) = 1 := by
    ext i j
    simp [Matrix.one_apply]
