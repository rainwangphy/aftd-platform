import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.GameTheoryEconomics.StrategicGame
import AFTD.Kb.GameTheoryEconomics.Profile

/-!
# EconCSLib.StrategicGame.welfare

Topic: equilibria   Node: 41ae82f0003d

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.welfare`. Lean proof by xbei, Claude (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

The social welfare of a profile: the sum of all players' payoffs. Requires `[Fintype N]` and `[AddCommMonoid U]`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} in
/-- The social welfare of a profile: the sum of all players' payoffs. Requires `[Fintype N]` and `[AddCommMonoid U]`. -/
noncomputable def EconCSLib.StrategicGame.welfare [Fintype N] [AddCommMonoid U]
    (G : EconCSLib.StrategicGame N U) (σ : G.Profile) : U :=
  ∑ i, G.payoff σ i
