import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDir
import AFTD.Kb.Physics.PhyslibWirtingerWeightedDirDeriv
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirEqWeightedDirDeriv
import AFTD.Kb.Physics.PhyslibWirtingerFderivWeightedDirDeriv
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirNeg

/-!
# Physlib.Wirtinger.fderiv_dWirtingerAntiDir

Topic: classical_mechanics   Node: 890c0145f285

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.fderiv_dWirtingerAntiDir`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Differentiating the anti-holomorphic directional derivative lands on the second real Fréchet derivative in the two slots.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  {f : V → ℂ} {u : V} in
/-- Differentiating the anti-holomorphic directional derivative lands on the second real Fréchet derivative in the two slots. -/
lemma Physlib.Wirtinger.fderiv_dWirtingerAntiDir (hf' : DifferentiableAt ℝ (fderiv ℝ f) u)
    (w a : V) :
    fderiv ℝ (fun p => dWirtingerAntiDir f w p) u a
      = (1 / 2 : ℂ) * (fderiv ℝ (fderiv ℝ f) u a w
          + Complex.I * fderiv ℝ (fderiv ℝ f) u a (Complex.I • w)) := by
  rw [dWirtingerAntiDir_eq_weightedDirDeriv, fderiv_weightedDirDeriv hf']
