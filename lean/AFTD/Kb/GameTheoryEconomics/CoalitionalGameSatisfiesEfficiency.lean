import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CoalitionalGame

/-!
# CoalitionalGame.SatisfiesEfficiency

Topic: general_equilibrium   Node: db3353e821b2

Provenance: formalization of a published result. Source: EconCSLib, `CoalitionalGame.SatisfiesEfficiency`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/CoalitionalGame/ShapleyValue.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A solution concept `φ` satisfies efficiency if payoffs sum to `v(N)`. [MSZ 18.2]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {N : Type*} [DecidableEq N] [Fintype N] in
variable (G : CoalitionalGame N ℝ) in
/-- A solution concept `φ` satisfies efficiency if payoffs sum to `v(N)`. [MSZ 18.2] -/
def CoalitionalGame.SatisfiesEfficiency (φ : CoalitionalGame N ℝ → N → ℝ) : Prop :=
  ∀ G : CoalitionalGame N ℝ, ∑ i : N, φ G i = G.v Finset.univ
