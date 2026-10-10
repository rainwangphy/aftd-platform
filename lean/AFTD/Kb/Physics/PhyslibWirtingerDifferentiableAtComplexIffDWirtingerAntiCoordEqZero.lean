import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiCoord
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDir
import AFTD.Kb.Physics.PhyslibWirtingerDifferentiableAtComplexIffDWirtingerAntiDirEqZero
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirEqZeroOfClinear
import AFTD.Kb.Physics.LinearMapCommutesIOfBasis
import AFTD.Kb.Physics.PhyslibWirtingerClinearOfDWirtingerAntiDirEqZero
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirNeg
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiCoordConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiCoordCoordProj

/-!
# Physlib.Wirtinger.differentiableAt_complex_iff_dWirtingerAntiCoord_eq_zero

Topic: classical_mechanics   Node: f979631dc8e2

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.differentiableAt_complex_iff_dWirtingerAntiCoord_eq_zero`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Coordinate.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Cauchy–Riemann in coordinates**, the form `∂̄_Ī W = 0` used in physics. Coordinate directions suffice by `LinearMap.commutesI_of_basis`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {ι : Type*} in
variable [Fintype ι] [DecidableEq ι] in
variable {f g : (ι → ℂ) → ℂ} in
/-- **Cauchy–Riemann in coordinates**, the form `∂̄_Ī W = 0` used in physics. Coordinate directions suffice by `LinearMap.commutesI_of_basis`. -/
theorem Physlib.Wirtinger.differentiableAt_complex_iff_dWirtingerAntiCoord_eq_zero
    (f : (ι → ℂ) → ℂ) (u : ι → ℂ) :
    DifferentiableAt ℂ f u ↔
      DifferentiableAt ℝ f u ∧ ∀ I, dWirtingerAntiCoord f I u = 0 := by
  rw [differentiableAt_complex_iff_dWirtingerAntiDir_eq_zero]
  refine and_congr_right fun _ => ⟨fun h I => h _, fun h v => ?_⟩
  refine dWirtingerAntiDir_eq_zero_of_clinear ?_
  exact LinearMap.commutesI_of_basis (fderiv ℝ f u : (ι → ℂ) →ₗ[ℝ] ℂ) (Pi.basisFun ℂ ι)
    (fun J => by simpa using clinear_of_dWirtingerAntiDir_eq_zero (h J)) v
