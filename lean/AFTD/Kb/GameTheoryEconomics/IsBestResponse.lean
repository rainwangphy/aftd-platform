import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameDeviate
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe
import AFTD.Kb.GameTheoryEconomics.StrategicGame
import AFTD.Kb.GameTheoryEconomics.Profile
import AFTD.Kb.GameTheoryEconomics.Deviate

/-!
# IsBestResponse

Topic: equilibria   Node: 0425e4d523dd

Provenance: formalization of a published result. Source: EconCSLib, `IsBestResponse`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/BestResponse.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Player `i` is playing a best response to profile `σ` in game `G` if no unilateral deviation to any strategy `s'` yields a higher payoff.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} [DecidableEq N] [Preorder U] in
open EconCSLib.StrategicGame in
/-- Player `i` is playing a best response to profile `σ` in game `G` if no unilateral deviation to any strategy `s'` yields a higher payoff. -/
def IsBestResponse (G : EconCSLib.StrategicGame N U) (σ : G.Profile) (i : N) : Prop :=
  ∀ s' : G.strategy i, G.payoff (EconCSLib.StrategicGame.deviate σ i s') i ≤ G.payoff σ i
