import AFTD.Prelude

/-!
# VAbs'

Topic: quantum_field_theory   Node: bf9c8982df23

Provenance: formalization of a published result. Source: Physlib, `VAbs'`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/FlavorPhysics/CKMMatrix/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The absolute value of the `(i,j)`th element of `V`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix Complex in
/-- The absolute value of the `(i,j)`th element of `V`. -/
@[simp]
noncomputable def VAbs' (V : unitaryGroup (Fin 3) ℂ) (i j : Fin 3) : ℝ := norm (V i j)
