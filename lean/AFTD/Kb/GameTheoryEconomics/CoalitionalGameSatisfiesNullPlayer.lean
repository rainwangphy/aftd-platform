import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CoalitionalGame
import AFTD.Kb.GameTheoryEconomics.CoalitionalGameIsNullPlayer

/-!
# CoalitionalGame.SatisfiesNullPlayer

Topic: general_equilibrium   Node: 47bbcb34d7ec

Provenance: formalization of a published result. Source: EconCSLib, `CoalitionalGame.SatisfiesNullPlayer`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/CoalitionalGame/ShapleyValue.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A solution concept satisfies the null player property. [MSZ 18.7]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {N : Type*} [DecidableEq N] [Fintype N] in
variable (G : CoalitionalGame N ℝ) in
/-- A solution concept satisfies the null player property. [MSZ 18.7] -/
def CoalitionalGame.SatisfiesNullPlayer (φ : CoalitionalGame N ℝ → N → ℝ) : Prop :=
  ∀ (G : CoalitionalGame N ℝ) (i : N), G.IsNullPlayer i → φ G i = 0
