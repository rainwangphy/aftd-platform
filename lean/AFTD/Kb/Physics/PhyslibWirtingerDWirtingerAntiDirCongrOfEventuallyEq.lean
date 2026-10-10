import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDir
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirApply
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirNeg

/-!
# Physlib.Wirtinger.dWirtingerAntiDir_congr_of_eventuallyEq

Topic: classical_mechanics   Node: 3f5785a3a8a4

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.dWirtingerAntiDir_congr_of_eventuallyEq`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The anti-holomorphic directional derivative depends only on the field near the point; dual of `dWirtingerDir_congr_of_eventuallyEq`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  {f : V → ℂ} {u : V} in
/-- The anti-holomorphic directional derivative depends only on the field near the point; dual of `dWirtingerDir_congr_of_eventuallyEq`. -/
lemma Physlib.Wirtinger.dWirtingerAntiDir_congr_of_eventuallyEq {f₁ f₂ : V → ℂ} {u : V}
    (h : f₁ =ᶠ[nhds u] f₂) (v : V) :
    dWirtingerAntiDir f₁ v u = dWirtingerAntiDir f₂ v u := by
  simp only [dWirtingerAntiDir_apply, h.fderiv_eq]
