import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsZeroSum
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsZeroSumDecidable
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsZeroSumExpectedPayoffNeg
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameExpectedPayoff
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameMixedProfile

/-!
# EconCSLib.StrategicGame.IsZeroSum.expectedPayoff_add_zero

Topic: equilibria   Node: 6aa664433c88

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.IsZeroSum.expectedPayoff_add_zero`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Mixed-strategy version of the zero-sum axiom: expected payoffs sum to `0`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {U : Type*} in
set_option linter.unusedSectionVars false in
variable [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
variable {G : EconCSLib.StrategicGame (Fin 2) U} in
variable [∀ i, Fintype (G.strategy i)] in
/-- Mixed-strategy version of the zero-sum axiom: expected payoffs sum to `0`. -/
@[simp] theorem EconCSLib.StrategicGame.IsZeroSum.expectedPayoff_add_zero
    (hzs : IsZeroSum G) (p : EconCSLib.StrategicGame.MixedProfile G) :
    EconCSLib.StrategicGame.expectedPayoff G p 0 + EconCSLib.StrategicGame.expectedPayoff G p 1 = 0 := by
  rw [hzs.expectedPayoff_neg]; ring
