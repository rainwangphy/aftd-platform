import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CoalitionalGame

/-!
# CoalitionalGame.marginalContrib

Topic: general_equilibrium   Node: 46f209b778fd

Provenance: formalization of a published result. Source: EconCSLib, `CoalitionalGame.marginalContrib`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/CoalitionalGame/ShapleyValue.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The marginal contribution of player `i` to coalition `S` (where `i ∉ S`).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {N : Type*} [DecidableEq N] [Fintype N] in
variable (G : CoalitionalGame N ℝ) in
/-- The marginal contribution of player `i` to coalition `S` (where `i ∉ S`). -/
def CoalitionalGame.marginalContrib (i : N) (S : Finset N) : ℝ :=
  G.v (insert i S) - G.v S
