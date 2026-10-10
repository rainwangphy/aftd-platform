import AFTD.Prelude

/-!
# diagPhase

Topic: quantum_field_theory   Node: 48978fd88a32

Provenance: formalization of a published result. Source: Physlib, `diagPhase`. Lean proof by Prabhoda Chandra Sarjapur, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/NeutrinoPhysics/Basic.lean (Copyright (c) 2025 Prabhoda Chandra Sarjapur. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

diagonal phase matrix from a real-valued function on indices
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix Complex in
/-- diagonal phase matrix from a real-valued function on indices -/
@[simp]
noncomputable def diagPhase (θ : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  λ i j => if i = j then cexp (I * θ i) else 0
