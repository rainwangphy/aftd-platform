import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsZeroSum
import AFTD.Kb.GameTheoryEconomics.StrategicGame
import AFTD.Kb.GameTheoryEconomics.Profile

/-!
# EconCSLib.StrategicGame.IsConstantSum

Topic: equilibria   Node: 5a97f8b8d7bd

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.IsConstantSum`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

A two-player game is constant-sum if payoffs sum to `c` at every profile.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {U : Type*} in
/-- A two-player game is constant-sum if payoffs sum to `c` at every profile. -/
def EconCSLib.StrategicGame.IsConstantSum [Add U] (G : EconCSLib.StrategicGame (Fin 2) U) (c : U) : Prop :=
  ∀ σ : G.Profile, G.payoff σ 0 + G.payoff σ 1 = c
