import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameDeviate

/-!
# EconCSLib.StrategicGame.IsExactPotential

Topic: equilibria   Node: 8773bd907bd8

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.IsExactPotential`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/PotentialGame.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

An exact potential function: the change in `Φ` equals the change in the deviating player's payoff.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} [DecidableEq N] in
open EconCSLib.StrategicGame in
variable [Sub U] [Preorder U] {G : EconCSLib.StrategicGame N U} in
/-- An exact potential function: the change in `Φ` equals the change in the deviating player's payoff. -/
def EconCSLib.StrategicGame.IsExactPotential (G : EconCSLib.StrategicGame N U) (Φ : G.Profile → U) : Prop :=
  ∀ (i : N) (σ : G.Profile) (s' : G.strategy i),
    G.payoff (deviate σ i s') i - G.payoff σ i =
    Φ (deviate σ i s') - Φ σ
