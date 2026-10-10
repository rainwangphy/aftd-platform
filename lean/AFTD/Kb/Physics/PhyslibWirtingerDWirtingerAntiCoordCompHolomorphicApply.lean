import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiCoord
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDir
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDir
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiCoordCompApply
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirEqOfClinear
import AFTD.Kb.Physics.PhyslibWirtingerClinearOfHolomorphic
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirEqZeroOfClinear
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirNeg
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirNeg
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiCoordConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiCoordCoordProj

/-!
# Physlib.Wirtinger.dWirtingerAntiCoord_comp_holomorphic_apply

Topic: classical_mechanics   Node: 2670f02c35fc

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.dWirtingerAntiCoord_comp_holomorphic_apply`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Coordinate.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The single-term coordinate chain rule for a holomorphic outer `g`, anti-holomorphic version, pointwise at `u`: `∂̄_I (g ∘ f) = deriv g (f u) · ∂̄_I f`. As in `dWirtingerCoord_comp_holomorphic_apply`, the `∂g/∂f̄` channel vanishes and `∂g/∂f` collapses to `deriv g (f u)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {ι : Type*} in
variable [Fintype ι] [DecidableEq ι] in
variable {g : ℂ → ℂ} {f : (ι → ℂ) → ℂ} in
/-- The single-term coordinate chain rule for a holomorphic outer `g`, anti-holomorphic version, pointwise at `u`: `∂̄_I (g ∘ f) = deriv g (f u) · ∂̄_I f`. As in `dWirtingerCoord_comp_holomorphic_apply`, the `∂g/∂f̄` channel vanishes and `∂g/∂f` collapses to `deriv g (f u)`. -/
lemma Physlib.Wirtinger.dWirtingerAntiCoord_comp_holomorphic_apply {u : (ι → ℂ)}
    (hg : DifferentiableAt ℂ g (f u)) (hf : DifferentiableAt ℝ f u) (I : ι) :
    dWirtingerAntiCoord (fun v => g (f v)) I u =
      deriv g (f u) * dWirtingerAntiCoord f I u := by
  rw [dWirtingerAntiCoord_comp_apply (hg.restrictScalars ℝ) hf I,
    dWirtingerDir_eq_of_clinear (clinear_of_holomorphic hg 1),
    DifferentiableAt.fderiv_restrictScalars ℝ hg, ContinuousLinearMap.coe_restrictScalars',
    fderiv_apply_one_eq_deriv,
    dWirtingerAntiDir_eq_zero_of_clinear (clinear_of_holomorphic hg 1), zero_mul, add_zero]
