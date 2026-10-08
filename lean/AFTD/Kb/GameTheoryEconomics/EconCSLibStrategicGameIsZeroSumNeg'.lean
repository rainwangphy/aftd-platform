import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsZeroSum
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame

/-!
# EconCSLib.StrategicGame.IsZeroSum.neg'

Topic: equilibria   Node: 33774c663c13

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.IsZeroSum.neg'`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

In a zero-sum game, player 0's payoff is the negation of player 1's.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {U : Type*} in
/-- In a zero-sum game, player 0's payoff is the negation of player 1's. -/
theorem EconCSLib.StrategicGame.IsZeroSum.neg' [AddGroup U]
    {G : EconCSLib.StrategicGame (Fin 2) U} (hzs : IsZeroSum G) (σ : G.Profile) :
    G.payoff σ 0 = - G.payoff σ 1 :=
  add_eq_zero_iff_eq_neg.mp (hzs σ)
