import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDir
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDir
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirApply
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirApply
import AFTD.Kb.Physics.PhyslibWirtingerFderivStarEq
import AFTD.Kb.Physics.PhyslibWirtingerRealLinearApplyEqWirtinger
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirNeg
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirNeg

/-!
# Physlib.Wirtinger.dWirtingerDir_comp

Topic: classical_mechanics   Node: fa2e72bd0a8e

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.dWirtingerDir_comp`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The two-term Wirtinger chain rule for `dWirtingerDir`, outer `g : ℂ → ℂ` and inner `f : V → ℂ`: `∂_v(g∘f) = (∂g/∂f)·∂_v f + (∂g/∂f̄)·∂_v f̄`. `realLinear_apply_eq_wirtinger` splits the chain rule's outer `ℝ`-linear factor into the `∂g/∂f`, `∂g/∂f̄` coefficients, each multiplying its inner directional derivative `∂_v f`, `∂_v f̄`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  {f : V → ℂ} {u : V} in
/-- The two-term Wirtinger chain rule for `dWirtingerDir`, outer `g : ℂ → ℂ` and inner `f : V → ℂ`: `∂_v(g∘f) = (∂g/∂f)·∂_v f + (∂g/∂f̄)·∂_v f̄`. `realLinear_apply_eq_wirtinger` splits the chain rule's outer `ℝ`-linear factor into the `∂g/∂f`, `∂g/∂f̄` coefficients, each multiplying its inner directional derivative `∂_v f`, `∂_v f̄`. -/
lemma Physlib.Wirtinger.dWirtingerDir_comp {g : ℂ → ℂ} (hg : DifferentiableAt ℝ g (f u))
    (hf : DifferentiableAt ℝ f u) (v : V) :
    dWirtingerDir (fun p => g (f p)) v u =
      dWirtingerDir g 1 (f u) * dWirtingerDir f v u
        + dWirtingerAntiDir g 1 (f u) * dWirtingerDir (fun p => star (f p)) v u := by
  simp only [dWirtingerDir_apply, dWirtingerAntiDir_apply]
  rw [show (fun p => g (f p)) = g ∘ f from rfl, fderiv_comp u hg hf, fderiv_star_eq hf]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    Complex.conjCLE_apply, Complex.star_def, smul_eq_mul, mul_one,
    realLinear_apply_eq_wirtinger (fderiv ℝ g (f u)) (fderiv ℝ f u v),
    realLinear_apply_eq_wirtinger (fderiv ℝ g (f u)) (fderiv ℝ f u (Complex.I • v))]
  ring
