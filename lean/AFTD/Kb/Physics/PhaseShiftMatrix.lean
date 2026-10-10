import AFTD.Prelude

/-!
# phaseShiftMatrix

Topic: quantum_field_theory   Node: 936832f8a59f

Provenance: formalization of a published result. Source: Physlib, `phaseShiftMatrix`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/FlavorPhysics/CKMMatrix/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given three real numbers `a b c` the complex matrix with `exp (I * a)` etc on the leading diagonal.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix Complex in
/-- Given three real numbers `a b c` the complex matrix with `exp (I * a)` etc on the leading diagonal. -/
@[simp]
noncomputable def phaseShiftMatrix (a b c : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  ![![cexp (I * a), 0, 0], ![0, cexp (I * b), 0], ![0, 0, cexp (I * c)]]
