import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CoalitionalGame

/-!
# CoalitionalGame.IsConvex

Topic: general_equilibrium   Node: 14f9134e9f74

Provenance: formalization of a published result. Source: EconCSLib, `CoalitionalGame.IsConvex`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/CoalitionalGame/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A game is convex if it satisfies the supermodularity condition. [MSZ 17.51] Requires `[LE U]` (addition comes from `[AddZeroClass U]`).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {N : Type*} [DecidableEq N] {U : Type*} [AddZeroClass U] in
variable (G : CoalitionalGame N U) in
/-- A game is convex if it satisfies the supermodularity condition. [MSZ 17.51] Requires `[LE U]` (addition comes from `[AddZeroClass U]`). -/
def CoalitionalGame.IsConvex [LE U] : Prop :=
  ∀ S T : Finset N, G.v (S ∪ T) + G.v (S ∩ T) ≥ G.v S + G.v T
