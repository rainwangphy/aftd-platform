import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CoalitionalGame

/-!
# CoalitionalGame.IsBalanced

Topic: general_equilibrium   Node: 6e4a5a1bdf1c

Provenance: formalization of a published result. Source: EconCSLib, `CoalitionalGame.IsBalanced`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/CoalitionalGame/Core.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A collection of coalitions is balanced if there exist positive weights summing to the characteristic vector of `N`. [MSZ 17.11]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {N : Type*} [DecidableEq N] [Fintype N] in
variable (G : CoalitionalGame N ℝ) in
/-- A collection of coalitions is balanced if there exist positive weights summing to the characteristic vector of `N`. [MSZ 17.11] -/
def CoalitionalGame.IsBalanced (𝒟 : Finset (Finset N)) : Prop :=
  ∃ δ : Finset N → ℝ,
    (∀ S ∈ 𝒟, δ S > 0) ∧
    ∀ i : N, ∑ S ∈ 𝒟.filter (i ∈ ·), δ S = 1
