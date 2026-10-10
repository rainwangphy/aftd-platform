import AFTD.Prelude
import AFTD.Kb.Physics.StandardModelGaugeGroupZ6UnitaryOfRoot
import AFTD.Kb.Physics.StandardModelGaugeGroupZ6UnitaryOfRootCoe

/-!
# StandardModel.gaugeGroupℤ₆SU2OfRoot

Topic: quantum_field_theory   Node: fe09268d39d0

Provenance: formalization of a published result. Source: Physlib, `StandardModel.gaugeGroupℤ₆SU2OfRoot`. Lean proof by Nikolai Kashcheev, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The `SU(2)` scalar matrix associated to a sixth root of unity.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Manifold in
open Matrix in
open Complex in
open ComplexConjugate in
/-- The `SU(2)` scalar matrix associated to a sixth root of unity. -/
noncomputable def StandardModel.gaugeGroupℤ₆SU2OfRoot (α : rootsOfUnity 6 ℂ) :
    specialUnitaryGroup (Fin 2) ℂ := by
  let u : unitary ℂ := gaugeGroupℤ₆UnitaryOfRoot α
  let z : ℂ := ((α : ℂˣ) : ℂ)
  let w : ℂ := star ((u ^ 3 : unitary ℂ) : ℂ)
  refine ⟨scalar (Fin 2) w, ?_⟩
  rw [mem_specialUnitaryGroup_iff]
  have hw : star w * w = 1 := by
    change star (star ((u ^ 3 : unitary ℂ) : ℂ)) *
      star ((u ^ 3 : unitary ℂ) : ℂ) = 1
    rw [star_star]
    exact (u ^ 3 : unitary ℂ).prop.2
  have hα : z ^ 6 = 1 := by
    simpa [z] using (mem_rootsOfUnity' 6 (α : ℂˣ)).mp α.prop
  have hw2 : w ^ 2 = 1 := by
    calc
      w ^ 2 = star (z ^ 6) := by
        simp [w, u, z, pow_succ]
        ring
      _ = 1 := by simp [hα]
  constructor
  · rw [mem_unitaryGroup_iff']
    rw [Matrix.scalar_apply, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_eq_one]
    funext i
    simpa [Pi.star_def] using hw
  · rw [Matrix.scalar_apply, Matrix.det_diagonal, Fin.prod_univ_two]
    simpa [pow_two] using hw2
