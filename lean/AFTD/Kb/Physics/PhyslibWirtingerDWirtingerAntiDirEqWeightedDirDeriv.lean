import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDir
import AFTD.Kb.Physics.PhyslibWirtingerWeightedDirDeriv
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirNeg

/-!
# Physlib.Wirtinger.dWirtingerAntiDir_eq_weightedDirDeriv

Topic: classical_mechanics   Node: 12d46f6460bb

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.dWirtingerAntiDir_eq_weightedDirDeriv`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A directional derivative is a `weightedDirDeriv`: anti-holomorphic with `c = i`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V]
  {f : V → ℂ} {u : V} in
/-- A directional derivative is a `weightedDirDeriv`: anti-holomorphic with `c = i`. -/
lemma Physlib.Wirtinger.dWirtingerAntiDir_eq_weightedDirDeriv (w : V) :
    (fun p => dWirtingerAntiDir f w p) = weightedDirDeriv f Complex.I w (Complex.I • w) :=
  rfl
