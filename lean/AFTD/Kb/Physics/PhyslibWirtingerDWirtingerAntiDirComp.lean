import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDir
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDir
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirApply
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirApply
import AFTD.Kb.Physics.PhyslibWirtingerFderivStarEq
import AFTD.Kb.Physics.PhyslibWirtingerRealLinearApplyEqWirtinger
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirNeg
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirNeg

/-!
# Physlib.Wirtinger.dWirtingerAntiDir_comp

Topic: classical_mechanics   Node: e32889012fed

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.dWirtingerAntiDir_comp`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The two-term Wirtinger chain rule for `dWirtingerAntiDir`, the anti-holomorphic dual of `dWirtingerDir_comp`: `∂̄_v(g∘f) = (∂g/∂f)·∂̄_v f + (∂g/∂f̄)·∂̄_v f̄`. Same outer `∂g/∂f`, `∂g/∂f̄` coefficients, now each multiplying its anti-holomorphic inner derivative `∂̄_v f`, `∂̄_v f̄`; same proof as `dWirtingerDir_comp`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  {f : V → ℂ} {u : V} in
/-- The two-term Wirtinger chain rule for `dWirtingerAntiDir`, the anti-holomorphic dual of `dWirtingerDir_comp`: `∂̄_v(g∘f) = (∂g/∂f)·∂̄_v f + (∂g/∂f̄)·∂̄_v f̄`. Same outer `∂g/∂f`, `∂g/∂f̄` coefficients, now each multiplying its anti-holomorphic inner derivative `∂̄_v f`, `∂̄_v f̄`; same proof as `dWirtingerDir_comp`. -/
lemma Physlib.Wirtinger.dWirtingerAntiDir_comp {g : ℂ → ℂ} (hg : DifferentiableAt ℝ g (f u))
    (hf : DifferentiableAt ℝ f u) (v : V) :
    dWirtingerAntiDir (fun p => g (f p)) v u =
      dWirtingerDir g 1 (f u) * dWirtingerAntiDir f v u
        + dWirtingerAntiDir g 1 (f u) * dWirtingerAntiDir (fun p => star (f p)) v u := by
  simp only [dWirtingerDir_apply, dWirtingerAntiDir_apply]
  rw [show (fun p => g (f p)) = g ∘ f from rfl, fderiv_comp u hg hf, fderiv_star_eq hf]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    Complex.conjCLE_apply, Complex.star_def, smul_eq_mul, mul_one,
    realLinear_apply_eq_wirtinger (fderiv ℝ g (f u)) (fderiv ℝ f u v),
    realLinear_apply_eq_wirtinger (fderiv ℝ g (f u)) (fderiv ℝ f u (Complex.I • v))]
  ring
