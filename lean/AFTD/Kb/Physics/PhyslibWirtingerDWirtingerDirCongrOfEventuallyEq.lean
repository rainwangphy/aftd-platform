import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDir
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirApply
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirNeg

/-!
# Physlib.Wirtinger.dWirtingerDir_congr_of_eventuallyEq

Topic: classical_mechanics   Node: ab8cc38478e6

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.dWirtingerDir_congr_of_eventuallyEq`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The holomorphic directional derivative depends only on the field near the point: fields agreeing on a neighbourhood have equal derivative.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  {f : V → ℂ} {u : V} in
/-- The holomorphic directional derivative depends only on the field near the point: fields agreeing on a neighbourhood have equal derivative. -/
lemma Physlib.Wirtinger.dWirtingerDir_congr_of_eventuallyEq {f₁ f₂ : V → ℂ} {u : V}
    (h : f₁ =ᶠ[nhds u] f₂) (v : V) :
    dWirtingerDir f₁ v u = dWirtingerDir f₂ v u := by
  simp only [dWirtingerDir_apply, h.fderiv_eq]
