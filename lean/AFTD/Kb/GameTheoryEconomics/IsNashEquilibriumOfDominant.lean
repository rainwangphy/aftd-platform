import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsWeaklyDominantIsBestResponse
import AFTD.Kb.GameTheoryEconomics.IsNashEquilibrium
import AFTD.Kb.GameTheoryEconomics.IsWeaklyDominant
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe

/-!
# IsNashEquilibrium.of_dominant

Topic: equilibria   Node: c165d765a191

Provenance: formalization of a published result. Source: EconCSLib, `IsNashEquilibrium.of_dominant`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/NashEquilibrium.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

T3: If every player has a weakly dominant strategy and `σ` assigns each player their dominant strategy, then `σ` is a Nash equilibrium.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} [DecidableEq N] [Preorder U] in
open EconCSLib.StrategicGame in
/-- T3: If every player has a weakly dominant strategy and `σ` assigns each player their dominant strategy, then `σ` is a Nash equilibrium. -/
theorem IsNashEquilibrium.of_dominant {G : EconCSLib.StrategicGame N U} {σ : G.Profile}
    (h : ∀ i : N, IsWeaklyDominant G i (σ i)) : IsNashEquilibrium G σ :=
  fun i => (h i).isBestResponse σ rfl
