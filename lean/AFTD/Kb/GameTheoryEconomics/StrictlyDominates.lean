import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameDeviate
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe

/-!
# StrictlyDominates

Topic: equilibria   Node: c66016516a2f

Provenance: formalization of a published result. Source: EconCSLib, `StrictlyDominates`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/Dominance.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Strategy `s` strictly dominates strategy `s'` for player `i`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} [DecidableEq N] [Preorder U] in
open EconCSLib.StrategicGame in
/-- Strategy `s` strictly dominates strategy `s'` for player `i`. -/
def StrictlyDominates (G : EconCSLib.StrategicGame N U) (i : N) (s s' : G.strategy i) : Prop :=
  ∀ σ : G.Profile, G.payoff (EconCSLib.StrategicGame.deviate σ i s') i < G.payoff (EconCSLib.StrategicGame.deviate σ i s) i
