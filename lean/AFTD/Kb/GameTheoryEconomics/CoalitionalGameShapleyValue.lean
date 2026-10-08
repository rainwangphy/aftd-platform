import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CoalitionalGame
import AFTD.Kb.GameTheoryEconomics.CoalitionalGameMarginalContrib

/-!
# CoalitionalGame.shapleyValue

Topic: general_equilibrium   Node: 344d5140e5bd

Provenance: formalization of a published result. Source: EconCSLib, `CoalitionalGame.shapleyValue`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/CoalitionalGame/ShapleyValue.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The Shapley value of player `i`. [MSZ 18.14, 18.17] `φᵢ(v) = ∑_{S ⊆ N\{i}} |S|!(|N|-|S|-1)!/|N|! · (v(S∪{i}) - v(S))`
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {N : Type*} [DecidableEq N] [Fintype N] in
variable (G : CoalitionalGame N ℝ) in
/-- The Shapley value of player `i`. [MSZ 18.14, 18.17] `φᵢ(v) = ∑_{S ⊆ N\{i}} |S|!(|N|-|S|-1)!/|N|! · (v(S∪{i}) - v(S))` -/
noncomputable def CoalitionalGame.shapleyValue (i : N) : ℝ :=
  ∑ S ∈ Finset.univ.filter (i ∉ ·),
    (Nat.factorial S.card * Nat.factorial (Fintype.card N - S.card - 1) : ℝ)
      / Nat.factorial (Fintype.card N)
      * G.marginalContrib i S
