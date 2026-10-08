import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CoalitionalGame

/-!
# CoalitionalGame.IsWinning

Topic: general_equilibrium   Node: a4f40f9ece43

Provenance: formalization of a published result. Source: EconCSLib, `CoalitionalGame.IsWinning`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/CoalitionalGame/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A coalition is winning in a simple game if its worth is 1. Requires `[One U]`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {N : Type*} [DecidableEq N] {U : Type*} [AddZeroClass U] in
variable (G : CoalitionalGame N U) in
/-- A coalition is winning in a simple game if its worth is 1. Requires `[One U]`. -/
def CoalitionalGame.IsWinning [One U] (S : Finset N) : Prop :=
  G.v S = 1
