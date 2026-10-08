import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsConstantSum
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.GameTheoryEconomics.IsNashEquilibrium
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsZeroSum
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsConstantSumNashPayoffEq
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsZeroSumDecidable
import AFTD.Kb.GameTheoryEconomics.StrategicGame
import AFTD.Kb.GameTheoryEconomics.Profile

/-!
# EconCSLib.StrategicGame.IsConstantSum.nash_payoff_eq_p1

Topic: equilibria   Node: 535571f89fe8

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.IsConstantSum.nash_payoff_eq_p1`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

In a constant-sum game, all Nash equilibria yield the same payoff for player 1.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open EconCSLib.StrategicGame in
variable {U : Type*} in
set_option linter.unusedSectionVars false in
variable [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
variable {G : EconCSLib.StrategicGame (Fin 2) U} in
/-- In a constant-sum game, all Nash equilibria yield the same payoff for player 1. -/
theorem EconCSLib.StrategicGame.IsConstantSum.nash_payoff_eq_p1
    {c : U} (hcs : IsConstantSum G c)
    {σ τ : G.Profile}
    (hσ : IsNashEquilibrium G σ) (hτ : IsNashEquilibrium G τ) :
    G.payoff σ 1 = G.payoff τ 1 := by
  linarith [hcs σ, hcs τ, hcs.nash_payoff_eq hσ hτ]
