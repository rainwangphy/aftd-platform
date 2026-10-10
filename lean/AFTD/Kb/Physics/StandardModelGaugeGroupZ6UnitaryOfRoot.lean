import AFTD.Prelude

/-!
# StandardModel.gaugeGroupℤ₆UnitaryOfRoot

Topic: quantum_field_theory   Node: 0966c0623782

Provenance: formalization of a published result. Source: Physlib, `StandardModel.gaugeGroupℤ₆UnitaryOfRoot`. Lean proof by Nikolai Kashcheev, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The unitary complex number associated to a sixth root of unity.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Manifold in
open Matrix in
open Complex in
open ComplexConjugate in
/-- The unitary complex number associated to a sixth root of unity. -/
noncomputable def StandardModel.gaugeGroupℤ₆UnitaryOfRoot (α : rootsOfUnity 6 ℂ) : unitary ℂ :=
  ⟨((α : ℂˣ) : ℂ), by
    have hα : ‖((α : ℂˣ) : ℂ)‖ = 1 := Complex.norm_eq_one_of_mem_rootsOfUnity α.prop
    constructor
    · rw [RCLike.star_def, Complex.conj_mul', hα]
      norm_num
    · rw [RCLike.star_def, Complex.mul_conj', hα]
      norm_num⟩
