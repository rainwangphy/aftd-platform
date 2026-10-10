import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDir
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDir
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirApply
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirApply
import AFTD.Kb.Physics.PhyslibWirtingerFderivStarEq
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirNeg
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirNeg

/-!
# Physlib.Wirtinger.dWirtingerAntiDir_star_comp

Topic: classical_mechanics   Node: e6b236db2838

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.dWirtingerAntiDir_star_comp`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Conjugating the function swaps the operators up to an outer conjugation: `∂̄_v f̄ = conj (∂_v f)`. Dual of `dWirtingerDir_star_comp`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  {f : V → ℂ} {u : V} in
/-- Conjugating the function swaps the operators up to an outer conjugation: `∂̄_v f̄ = conj (∂_v f)`. Dual of `dWirtingerDir_star_comp`. -/
lemma Physlib.Wirtinger.dWirtingerAntiDir_star_comp (hf : DifferentiableAt ℝ f u) (v : V) :
    dWirtingerAntiDir (fun p => star (f p)) v u = star (dWirtingerDir f v u) := by
  rw [dWirtingerAntiDir_apply, dWirtingerDir_apply, fderiv_star_eq hf]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    Complex.conjCLE_apply, Complex.star_def, map_mul, map_sub, map_div₀, map_one,
    map_ofNat, Complex.conj_I]
  ring
