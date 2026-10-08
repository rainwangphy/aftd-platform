import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CoalitionalGame

/-!
# CoalitionalGame.IsBalancedGame

Topic: general_equilibrium   Node: e78707bfb9dc

Provenance: formalization of a published result. Source: EconCSLib, `CoalitionalGame.IsBalancedGame`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/CoalitionalGame/Core.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A game is balanced if every balanced collection satisfies the superadditivity-like condition. [MSZ 17.14 premise]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {N : Type*} [DecidableEq N] [Fintype N] in
variable (G : CoalitionalGame N ℝ) in
/-- A game is balanced if every balanced collection satisfies the superadditivity-like condition. [MSZ 17.14 premise] -/
def CoalitionalGame.IsBalancedGame : Prop :=
  ∀ (𝒟 : Finset (Finset N)) (δ : Finset N → ℝ),
    (∀ S ∈ 𝒟, δ S > 0) →
    (∀ i : N, ∑ S ∈ 𝒟.filter (i ∈ ·), δ S = 1) →
    ∑ S ∈ 𝒟, δ S * G.v S ≤ G.v Finset.univ
