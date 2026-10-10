import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDir
import AFTD.Kb.Physics.PhyslibWirtingerWeightedDirDeriv
import AFTD.Kb.Physics.PhyslibWirtingerHasFDerivAtWeightedDirDeriv
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirNeg

/-!
# Physlib.Wirtinger.differentiableAt_dWirtingerDir

Topic: classical_mechanics   Node: 2dae38dde5b2

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.differentiableAt_dWirtingerDir`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

On a `C²` field the holomorphic directional derivative is itself real-differentiable.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  {f : V → ℂ} {u : V} in
/-- On a `C²` field the holomorphic directional derivative is itself real-differentiable. -/
lemma Physlib.Wirtinger.differentiableAt_dWirtingerDir (hf2 : ContDiffAt ℝ 2 f u) (v : V) :
    DifferentiableAt ℝ (fun p => dWirtingerDir f v p) u := by
  exact (hasFDerivAt_weightedDirDeriv
    ((hf2.fderiv_right (m := 1) le_rfl).differentiableAt one_ne_zero) _ _ _).differentiableAt
