import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.GameTheoryEconomics.IsBestResponse
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameDeviate
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe
import AFTD.Kb.GameTheoryEconomics.StrategicGame
import AFTD.Kb.GameTheoryEconomics.Profile

/-!
# IsBestResponse.congr_payoff

Topic: equilibria   Node: 65d39b67ecc7

Provenance: formalization of a published result. Source: EconCSLib, `IsBestResponse.congr_payoff`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/BestResponse.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

T1: Best response depends only on player `i`'s payoff column.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} [DecidableEq N] [Preorder U] in
open EconCSLib.StrategicGame in
/-- T1: Best response depends only on player `i`'s payoff column. -/
theorem IsBestResponse.congr_payoff (G : EconCSLib.StrategicGame N U) (σ : G.Profile) (i : N)
    {payoff' : G.Profile → N → U}
    (h : ∀ τ : G.Profile, payoff' τ i = G.payoff τ i) :
    IsBestResponse G σ i ↔
    IsBestResponse { G with payoff := payoff' } σ i := by
  simp [IsBestResponse, h]
