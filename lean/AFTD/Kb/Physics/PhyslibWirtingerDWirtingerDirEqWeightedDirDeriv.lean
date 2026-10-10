import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDir
import AFTD.Kb.Physics.PhyslibWirtingerWeightedDirDeriv
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirNeg

/-!
# Physlib.Wirtinger.dWirtingerDir_eq_weightedDirDeriv

Topic: classical_mechanics   Node: cdfa7e8e52d2

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.dWirtingerDir_eq_weightedDirDeriv`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A directional derivative is a `weightedDirDeriv`: holomorphic with `c = -i`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  {f : V → ℂ} {u : V} in
/-- A directional derivative is a `weightedDirDeriv`: holomorphic with `c = -i`. -/
lemma Physlib.Wirtinger.dWirtingerDir_eq_weightedDirDeriv (v : V) :
    (fun p => dWirtingerDir f v p) = weightedDirDeriv f (-Complex.I) v (Complex.I • v) :=
  rfl
