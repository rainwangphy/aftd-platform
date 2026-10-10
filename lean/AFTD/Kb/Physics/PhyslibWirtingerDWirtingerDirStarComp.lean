import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDir
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDir
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirApply
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirApply
import AFTD.Kb.Physics.PhyslibWirtingerFderivStarEq
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirNeg
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirNeg
import AFTD.Kb.Physics.CondensedMatterTightBindingChainQuantaWaveNumberExpSubOne

/-!
# Physlib.Wirtinger.dWirtingerDir_star_comp

Topic: classical_mechanics   Node: deb27114003e

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.dWirtingerDir_star_comp`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Conjugating the function swaps the operators up to an outer conjugation: `∂_v f̄ = conj (∂̄_v f)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  {f : V → ℂ} {u : V} in
/-- Conjugating the function swaps the operators up to an outer conjugation: `∂_v f̄ = conj (∂̄_v f)`. -/
lemma Physlib.Wirtinger.dWirtingerDir_star_comp (hf : DifferentiableAt ℝ f u) (v : V) :
    dWirtingerDir (fun p => star (f p)) v u = star (dWirtingerAntiDir f v u) := by
  rw [dWirtingerDir_apply, dWirtingerAntiDir_apply, fderiv_star_eq hf]
  simp only [one_div, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousAlgEquiv.coeCLE_apply, Complex.conjCAE_apply, star_mul', star_inv₀,
    star_ofNat, star_add, RCLike.star_def, Complex.conj_I, neg_mul,
    mul_eq_mul_left_iff, inv_eq_zero, OfNat.ofNat_ne_zero, or_false]
  ring
