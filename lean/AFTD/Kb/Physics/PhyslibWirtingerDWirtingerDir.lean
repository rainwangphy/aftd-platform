import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerWeightedDirDeriv

/-!
# Physlib.Wirtinger.dWirtingerDir

Topic: classical_mechanics   Node: 078544da2d65

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.dWirtingerDir`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The holomorphic directional Wirtinger derivative `∂_v f = (1/2)(d_v f − i·d_{i·v} f)` of `f : V → ℂ` along the direction vector `v : V`, the `weightedDirDeriv` at `c = -i`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  {f : V → ℂ} {u : V} in
/-- The holomorphic directional Wirtinger derivative `∂_v f = (1/2)(d_v f − i·d_{i·v} f)` of `f : V → ℂ` along the direction vector `v : V`, the `weightedDirDeriv` at `c = -i`. -/
noncomputable def Physlib.Wirtinger.dWirtingerDir (f : V → ℂ) (v u : V) : ℂ :=
  weightedDirDeriv f (-Complex.I) v (Complex.I • v) u
