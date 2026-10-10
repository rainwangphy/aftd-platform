import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiCoord
import AFTD.Kb.Physics.PhyslibWirtingerConjCLM
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDir
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDir
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirCompConjLinear
import AFTD.Kb.Physics.PhyslibWirtingerConjCLMSmulI
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirEqOfClinear
import AFTD.Kb.Physics.PhyslibWirtingerClinearOfHolomorphic
import AFTD.Kb.Physics.PhyslibWirtingerConjCLMApply
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirNeg
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirNeg
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiCoordConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiCoordCoordProj

/-!
# Physlib.Wirtinger.dWirtingerAntiCoord_eq_complex_fderiv_apply

Topic: classical_mechanics   Node: 874178faa729

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.dWirtingerAntiCoord_eq_complex_fderiv_apply`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Coordinate.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For an anti-holomorphic function the anti-holomorphic Wirtinger derivative equals the complex Fréchet derivative of `g` at `star u` along the slot-I real coordinate direction, `∂̄_I (g ∘ star) = fderiv ℂ g (star u) (Pi.single I 1)`. Dual of `dWirtingerCoord_eq_complex_fderiv_apply`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {ι : Type*} in
variable [Fintype ι] [DecidableEq ι] in
variable {f g : (ι → ℂ) → ℂ} in
/-- For an anti-holomorphic function the anti-holomorphic Wirtinger derivative equals the complex Fréchet derivative of `g` at `star u` along the slot-I real coordinate direction, `∂̄_I (g ∘ star) = fderiv ℂ g (star u) (Pi.single I 1)`. Dual of `dWirtingerCoord_eq_complex_fderiv_apply`. -/
lemma Physlib.Wirtinger.dWirtingerAntiCoord_eq_complex_fderiv_apply {u : (ι → ℂ)}
    (hg : DifferentiableAt ℂ g (star u)) (I : ι) :
    dWirtingerAntiCoord (fun v : (ι → ℂ) => g (star v)) I u =
      fderiv ℂ g (star u) (Pi.single I 1) := by
  have hgr : DifferentiableAt ℝ g (conjCLM u) := hg.restrictScalars ℝ
  change dWirtingerAntiDir (fun v : (ι → ℂ) => g (conjCLM v)) (Pi.single I 1) u
      = fderiv ℂ g (star u) (Pi.single I 1)
  rw [dWirtingerAntiDir_comp_conjLinear conjCLM_smul_I hgr]
  simp only [conjCLM_apply, Pi.star_single, star_one]
  rw [dWirtingerDir_eq_of_clinear (clinear_of_holomorphic hg _),
    DifferentiableAt.fderiv_restrictScalars ℝ hg, ContinuousLinearMap.coe_restrictScalars']
