import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameMixedStrategy
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGamePureToMixed
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsCompletelyMixed

/-!
# EconCSLib.StrategicGame.pureToMixed_not_isCompletelyMixed_of_ne

Topic: equilibria   Node: 0190e7914219

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.pureToMixed_not_isCompletelyMixed_of_ne`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/MixedStrategy.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

A point-mass mixed strategy is not completely mixed when there is another pure strategy available.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {N U : Type*} [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
/-- A point-mass mixed strategy is not completely mixed when there is another pure strategy available. -/
theorem EconCSLib.StrategicGame.pureToMixed_not_isCompletelyMixed_of_ne {G : EconCSLib.StrategicGame N ℚ}
    {i : N} [Fintype (G.strategy i)] [DecidableEq (G.strategy i)]
    {s₀ s₁ : G.strategy i} (h : s₁ ≠ s₀) :
    ¬ IsCompletelyMixed G (pureToMixed (G := G) (i := i) s₀) := by
  intro hcm
  have hpos := hcm s₁
  simp [pureToMixed, h] at hpos
