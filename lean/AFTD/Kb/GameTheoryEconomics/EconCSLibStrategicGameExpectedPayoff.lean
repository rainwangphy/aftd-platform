import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameMixedProfile
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameMixedStrategy
import AFTD.Kb.GameTheoryEconomics.Profile
import AFTD.Kb.GameTheoryEconomics.StrategicGame

/-!
# EconCSLib.StrategicGame.expectedPayoff

Topic: equilibria   Node: d817425556b7

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.expectedPayoff`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/MixedStrategy.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Expected payoff for player `who` under mixed profile `p`. `EU(p, who) = ∑_{σ : Profile} (∏_i p_i(σ_i)) · payoff(σ, who)` Requires `[Fintype N]` (to sum over all profiles) and `[∀ i, Fintype (G.strategy i)]` (finite strategy sets).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {N U : Type*} [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
/-- Expected payoff for player `who` under mixed profile `p`. `EU(p, who) = ∑_{σ : Profile} (∏_i p_i(σ_i)) · payoff(σ, who)` Requires `[Fintype N]` (to sum over all profiles) and `[∀ i, Fintype (G.strategy i)]` (finite strategy sets). -/
def EconCSLib.StrategicGame.expectedPayoff
    (G : EconCSLib.StrategicGame N U)
    [Fintype N] [DecidableEq N] [∀ i, Fintype (G.strategy i)]
    (p : MixedProfile G) (who : N) : U :=
  ∑ σ : G.Profile, (∏ i : N, (p i).val (σ i)) * G.payoff σ who
