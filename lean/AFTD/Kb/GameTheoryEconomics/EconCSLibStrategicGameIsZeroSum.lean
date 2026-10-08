import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame

/-!
# EconCSLib.StrategicGame.IsZeroSum

Topic: equilibria   Node: 3b7daac77ced

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.IsZeroSum`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

A two-player game is zero-sum if payoffs sum to zero at every profile. [MSZ 4.39]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {U : Type*} in
/-- A two-player game is zero-sum if payoffs sum to zero at every profile. [MSZ 4.39] -/
def EconCSLib.StrategicGame.IsZeroSum [Add U] [Zero U] (G : EconCSLib.StrategicGame (Fin 2) U) : Prop :=
  ∀ σ : G.Profile, G.payoff σ 0 + G.payoff σ 1 = 0
