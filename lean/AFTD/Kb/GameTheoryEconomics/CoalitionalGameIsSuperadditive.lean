import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CoalitionalGame

/-!
# CoalitionalGame.IsSuperadditive

Topic: general_equilibrium   Node: 553f5e88ba2e

Provenance: formalization of a published result. Source: EconCSLib, `CoalitionalGame.IsSuperadditive`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/CoalitionalGame/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A game is superadditive if the worth of the union of disjoint coalitions is at least the sum of their worths. [MSZ 16.8] Requires `[LE U]` (addition comes from the `[AddZeroClass U]` section variable).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {N : Type*} [DecidableEq N] {U : Type*} [AddZeroClass U] in
variable (G : CoalitionalGame N U) in
/-- A game is superadditive if the worth of the union of disjoint coalitions is at least the sum of their worths. [MSZ 16.8] Requires `[LE U]` (addition comes from the `[AddZeroClass U]` section variable). -/
def CoalitionalGame.IsSuperadditive [LE U] : Prop :=
  ∀ S T : Finset N, Disjoint S T → G.v (S ∪ T) ≥ G.v S + G.v T
