import AFTD.Prelude

/-!
# StandardModel.gaugeGroupℤ₆SU3OfRoot

Topic: quantum_field_theory   Node: 9c56b5c01567

Provenance: formalization of a published result. Source: Physlib, `StandardModel.gaugeGroupℤ₆SU3OfRoot`. Lean proof by Nikolai Kashcheev, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The `SU(3)` scalar matrix associated to a sixth root of unity.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Manifold in
open Matrix in
open Complex in
open ComplexConjugate in
/-- The `SU(3)` scalar matrix associated to a sixth root of unity. -/
noncomputable def StandardModel.gaugeGroupℤ₆SU3OfRoot (α : rootsOfUnity 6 ℂ) :
    specialUnitaryGroup (Fin 3) ℂ :=
  let z : ℂ := ((α : ℂˣ) : ℂ)
  ⟨scalar (Fin 3) (z ^ 2), by
    rw [mem_specialUnitaryGroup_iff]
    have hz : ‖z‖ = 1 := by
      simpa [z] using Complex.norm_eq_one_of_mem_rootsOfUnity α.prop
    have hz2 : star (z ^ 2) * z ^ 2 = 1 := by
      rw [RCLike.star_def, Complex.conj_mul', Complex.norm_pow, hz]
      norm_num
    constructor
    · rw [mem_unitaryGroup_iff']
      rw [Matrix.scalar_apply, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul_diagonal, Matrix.diagonal_eq_one]
      funext i
      simpa [Pi.star_def] using hz2
    · have hα : z ^ 6 = 1 := by
        simpa [z] using (mem_rootsOfUnity' 6 (α : ℂˣ)).mp α.prop
      rw [Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_three]
      calc
        z ^ 2 * z ^ 2 * z ^ 2 = z ^ 6 := by ring
        _ = 1 := hα⟩
