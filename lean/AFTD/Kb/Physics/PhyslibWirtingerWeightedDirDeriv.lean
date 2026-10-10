import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsSimplePendulumSeparatrixEnergy

/-!
# Physlib.Wirtinger.weightedDirDeriv

Topic: classical_mechanics   Node: 1147859df22b

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.weightedDirDeriv`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The base-point field `p ↦ (1/2)(d_{b₁} f + c·d_{b₂} f)`, a weighted combination of the real Fréchet derivative of `f` along two directions `b₁`, `b₂`. The directional Wirtinger operators are its two specializations: `dWirtingerDir f v` at `c = -i`, `(b₁, b₂) = (v, i·v)`, and `dWirtingerAntiDir f v` at `c = i`. Keeping `b₁`, `b₂` free lets §G differentiate it a second time once and reuse the bridge for both operators.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  {f : V → ℂ} {u : V} in
/-- The base-point field `p ↦ (1/2)(d_{b₁} f + c·d_{b₂} f)`, a weighted combination of the real Fréchet derivative of `f` along two directions `b₁`, `b₂`. The directional Wirtinger operators are its two specializations: `dWirtingerDir f v` at `c = -i`, `(b₁, b₂) = (v, i·v)`, and `dWirtingerAntiDir f v` at `c = i`. Keeping `b₁`, `b₂` free lets §G differentiate it a second time once and reuse the bridge for both operators. -/
noncomputable def Physlib.Wirtinger.weightedDirDeriv (f : V → ℂ) (c : ℂ) (b₁ b₂ : V) : V → ℂ :=
  fun p => (1 / 2 : ℂ) * (fderiv ℝ f p b₁ + c * fderiv ℝ f p b₂)
