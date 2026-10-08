import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CoalitionalGame

/-!
# CoalitionalGame.IsNullPlayer

Topic: general_equilibrium   Node: 32f2e1fdc08a

Provenance: formalization of a published result. Source: EconCSLib, `CoalitionalGame.IsNullPlayer`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/CoalitionalGame/ShapleyValue.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A player is a null player if they add nothing to any coalition. [MSZ 18.6]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {N : Type*} [DecidableEq N] [Fintype N] in
variable (G : CoalitionalGame N ℝ) in
/-- A player is a null player if they add nothing to any coalition. [MSZ 18.6] -/
def CoalitionalGame.IsNullPlayer (i : N) : Prop :=
  ∀ S : Finset N, i ∉ S → G.v (insert i S) = G.v S
