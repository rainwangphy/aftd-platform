import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDir
import AFTD.Kb.Physics.PhyslibWirtingerWeightedDirDeriv
import AFTD.Kb.Physics.PhyslibWirtingerHasFDerivAtWeightedDirDeriv
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirNeg

/-!
# Physlib.Wirtinger.differentiableAt_dWirtingerAntiDir

Topic: classical_mechanics   Node: 5471149a2545

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.differentiableAt_dWirtingerAntiDir`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

On a `C²` field the anti-holomorphic directional derivative is itself real-differentiable.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  {f : V → ℂ} {u : V} in
/-- On a `C²` field the anti-holomorphic directional derivative is itself real-differentiable. -/
lemma Physlib.Wirtinger.differentiableAt_dWirtingerAntiDir (hf2 : ContDiffAt ℝ 2 f u) (w : V) :
    DifferentiableAt ℝ (fun p => dWirtingerAntiDir f w p) u := by
  exact (hasFDerivAt_weightedDirDeriv
    ((hf2.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero) _ _ _).differentiableAt
