import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CoalitionalGame

/-!
# CoalitionalGame.IsMonotonic

Topic: general_equilibrium   Node: 1837b31b8fdf

Provenance: formalization of a published result. Source: EconCSLib, `CoalitionalGame.IsMonotonic`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/CoalitionalGame/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A game is monotonic if larger coalitions are worth at least as much. [MSZ 16.10] Requires `[LE U]`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {N : Type*} [DecidableEq N] {U : Type*} [AddZeroClass U] in
variable (G : CoalitionalGame N U) in
/-- A game is monotonic if larger coalitions are worth at least as much. [MSZ 16.10] Requires `[LE U]`. -/
def CoalitionalGame.IsMonotonic [LE U] : Prop :=
  ∀ S T : Finset N, S ⊆ T → G.v S ≤ G.v T
