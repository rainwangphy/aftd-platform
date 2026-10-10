import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDir
import AFTD.Kb.Physics.PhyslibWirtingerWeightedDirDeriv
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirEqWeightedDirDeriv
import AFTD.Kb.Physics.PhyslibWirtingerFderivWeightedDirDeriv
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirNeg

/-!
# Physlib.Wirtinger.fderiv_dWirtingerDir

Topic: classical_mechanics   Node: 094b2c6c26d7

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.fderiv_dWirtingerDir`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Differentiating the holomorphic directional derivative lands on the second real Fréchet derivative in the two slots.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  {f : V → ℂ} {u : V} in
/-- Differentiating the holomorphic directional derivative lands on the second real Fréchet derivative in the two slots. -/
lemma Physlib.Wirtinger.fderiv_dWirtingerDir (hf' : DifferentiableAt ℝ (fderiv ℝ f) u)
    (v a : V) :
    fderiv ℝ (fun p => dWirtingerDir f v p) u a
      = (1 / 2 : ℂ) * (fderiv ℝ (fderiv ℝ f) u a v
          - Complex.I * fderiv ℝ (fderiv ℝ f) u a (Complex.I • v)) := by
  rw [dWirtingerDir_eq_weightedDirDeriv, fderiv_weightedDirDeriv hf', neg_mul, ← sub_eq_add_neg]
