import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CoalitionalGame

/-!
# CoalitionalGame.IsAdditive

Topic: general_equilibrium   Node: 9c5802af2bcc

Provenance: formalization of a published result. Source: EconCSLib, `CoalitionalGame.IsAdditive`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/CoalitionalGame/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A game is additive if `v(S) = ∑_{i ∈ S} v({i})`. [MSZ 17.41] Requires `[AddCommMonoid U]`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {N : Type*} [DecidableEq N] {U : Type*} [AddZeroClass U] in
variable (G : CoalitionalGame N U) in
/-- A game is additive if `v(S) = ∑_{i ∈ S} v({i})`. [MSZ 17.41] Requires `[AddCommMonoid U]`. -/
def CoalitionalGame.IsAdditive [AddCommMonoid U] : Prop :=
  ∀ S : Finset N, G.v S = ∑ i ∈ S, G.v {i}
