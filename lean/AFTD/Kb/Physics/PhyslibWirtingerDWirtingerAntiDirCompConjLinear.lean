import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDir
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDir
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirApply
import AFTD.Kb.Physics.PhyslibWirtingerFderivCompClmApply
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirApply
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirNeg
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirNeg

/-!
# Physlib.Wirtinger.dWirtingerAntiDir_comp_conjLinear

Topic: classical_mechanics   Node: ff72be51b9fb

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.dWirtingerAntiDir_comp_conjLinear`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Dual of `dWirtingerDir_comp_conjLinear`: the anti-holomorphic derivative of `g ∘ L` at `u` is the holomorphic derivative of `g` at the mapped point `L u`, in the mapped direction `L v`: `∂̄_v(g ∘ L)` at `u` equals `∂_{L v} g` at `L u`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  {f : V → ℂ} {u : V} in
variable {V' : Type*} [NormedAddCommGroup V'] [NormedSpace ℝ V'] [NormedSpace ℂ V'] in
/-- Dual of `dWirtingerDir_comp_conjLinear`: the anti-holomorphic derivative of `g ∘ L` at `u` is the holomorphic derivative of `g` at the mapped point `L u`, in the mapped direction `L v`: `∂̄_v(g ∘ L)` at `u` equals `∂_{L v} g` at `L u`. -/
lemma Physlib.Wirtinger.dWirtingerAntiDir_comp_conjLinear {g : V' → ℂ} {L : V →L[ℝ] V'} {u : V}
    (hL : ∀ x : V, L (Complex.I • x) = -(Complex.I • L x))
    (hg : DifferentiableAt ℝ g (L u)) (v : V) :
    dWirtingerAntiDir (fun p => g (L p)) v u = dWirtingerDir g (L v) (L u) := by
  simp only [dWirtingerDir_apply, dWirtingerAntiDir_apply, fderiv_comp_clm_apply hg, hL,
    map_neg]
  ring
