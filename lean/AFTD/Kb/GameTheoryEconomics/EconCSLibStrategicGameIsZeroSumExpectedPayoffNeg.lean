import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameMixedStrategy
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsZeroSumNeg
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsZeroSum
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsZeroSumDecidable
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameExpectedPayoff
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameMixedProfile

/-!
# EconCSLib.StrategicGame.IsZeroSum.expectedPayoff_neg

Topic: equilibria   Node: 5d16b019936c

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.IsZeroSum.expectedPayoff_neg`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

In a zero-sum game, player 1's expected payoff is the negation of player 0's.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {U : Type*} in
set_option linter.unusedSectionVars false in
variable [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
variable {G : EconCSLib.StrategicGame (Fin 2) U} in
variable [∀ i, Fintype (G.strategy i)] in
/-- In a zero-sum game, player 1's expected payoff is the negation of player 0's. -/
theorem EconCSLib.StrategicGame.IsZeroSum.expectedPayoff_neg
    (hzs : IsZeroSum G) (p : EconCSLib.StrategicGame.MixedProfile G) :
    EconCSLib.StrategicGame.expectedPayoff G p 1
      = -(EconCSLib.StrategicGame.expectedPayoff G p 0) := by
  unfold EconCSLib.StrategicGame.expectedPayoff
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  rw [hzs.neg σ]
  ring
