import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDir
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirEqZeroOfClinear
import AFTD.Kb.Physics.ContinuousLinearMapComplexOfCommutesI
import AFTD.Kb.Physics.PhyslibWirtingerClinearOfDWirtingerAntiDirEqZero
import AFTD.Kb.Physics.ContinuousLinearMapComplexOfCommutesIApply
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirNeg

/-!
# Physlib.Wirtinger.differentiableAt_complex_iff_dWirtingerAntiDir_eq_zero

Topic: classical_mechanics   Node: eeb65a28b370

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.differentiableAt_complex_iff_dWirtingerAntiDir_eq_zero`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Cauchy–Riemann.** `f` is `ℂ`-differentiable at `u` iff it is real-differentiable there and every anti-holomorphic Wirtinger derivative vanishes. Real differentiability is needed: `fderiv` is `0` where `f` is not differentiable.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  {f : V → ℂ} {u : V} in
variable [IsScalarTower ℝ ℂ V] in
/-- **Cauchy–Riemann.** `f` is `ℂ`-differentiable at `u` iff it is real-differentiable there and every anti-holomorphic Wirtinger derivative vanishes. Real differentiability is needed: `fderiv` is `0` where `f` is not differentiable. -/
theorem Physlib.Wirtinger.differentiableAt_complex_iff_dWirtingerAntiDir_eq_zero (f : V → ℂ) (u : V) :
    DifferentiableAt ℂ f u ↔
      DifferentiableAt ℝ f u ∧ ∀ v, dWirtingerAntiDir f v u = 0 := by
  constructor
  · intro hf
    refine ⟨hf.restrictScalars ℝ, fun v => ?_⟩
    refine dWirtingerAntiDir_eq_zero_of_clinear ?_
    rw [DifferentiableAt.fderiv_restrictScalars ℝ hf, ContinuousLinearMap.coe_restrictScalars',
      map_smul]
  · rintro ⟨hR, hv⟩
    rw [differentiableAt_iff_restrictScalars ℝ hR]
    exact ⟨ContinuousLinearMap.complexOfCommutesI (fderiv ℝ f u)
      (fun v => clinear_of_dWirtingerAntiDir_eq_zero (hv v)), rfl⟩
