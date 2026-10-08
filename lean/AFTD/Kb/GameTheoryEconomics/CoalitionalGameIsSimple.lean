import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CoalitionalGame

/-!
# CoalitionalGame.IsSimple

Topic: general_equilibrium   Node: 6ec70a1988f6

Provenance: formalization of a published result. Source: EconCSLib, `CoalitionalGame.IsSimple`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/CoalitionalGame/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A game is simple if every coalition's worth is 0 or 1, and the grand coalition's worth is 1. [MSZ 16.2] Requires `[Fintype N]` and `[One U]`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {N : Type*} [DecidableEq N] {U : Type*} [AddZeroClass U] in
variable (G : CoalitionalGame N U) in
/-- A game is simple if every coalition's worth is 0 or 1, and the grand coalition's worth is 1. [MSZ 16.2] Requires `[Fintype N]` and `[One U]`. -/
def CoalitionalGame.IsSimple [Fintype N] [One U] : Prop :=
  (∀ S : Finset N, G.v S = 0 ∨ G.v S = 1) ∧ G.v Finset.univ = 1
