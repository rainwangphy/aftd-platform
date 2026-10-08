import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CoalitionalGame

/-!
# CoalitionalGame.AreSymmetric

Topic: general_equilibrium   Node: 92dac32757f3

Provenance: formalization of a published result. Source: EconCSLib, `CoalitionalGame.AreSymmetric`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/CoalitionalGame/ShapleyValue.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Two players are symmetric if swapping them doesn't change any coalition's worth.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {N : Type*} [DecidableEq N] [Fintype N] in
variable (G : CoalitionalGame N ℝ) in
/-- Two players are symmetric if swapping them doesn't change any coalition's worth. -/
def CoalitionalGame.AreSymmetric (i j : N) : Prop :=
  ∀ S : Finset N, i ∉ S → j ∉ S → G.v (insert i S) = G.v (insert j S)
