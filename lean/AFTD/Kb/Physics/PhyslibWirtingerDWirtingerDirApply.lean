import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDir
import AFTD.Kb.Physics.PhyslibWirtingerWeightedDirDeriv
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumSeparatrixEnergy

/-!
# Physlib.Wirtinger.dWirtingerDir_apply

Topic: classical_mechanics   Node: 9e5c2600ea74

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.dWirtingerDir_apply`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Definitional unfolding of `dWirtingerDir` to the explicit Wirtinger combination, used to expand the outer operator of a composition without touching the inner one.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  {f : V → ℂ} {u : V} in
/-- Definitional unfolding of `dWirtingerDir` to the explicit Wirtinger combination, used to expand the outer operator of a composition without touching the inner one. -/
lemma Physlib.Wirtinger.dWirtingerDir_apply (g : V → ℂ) (v u : V) :
    dWirtingerDir g v u
      = (1 / 2 : ℂ) * (fderiv ℝ g u v - Complex.I * fderiv ℝ g u (Complex.I • v)) := by
  simp only [dWirtingerDir, weightedDirDeriv, neg_mul, ← sub_eq_add_neg]
