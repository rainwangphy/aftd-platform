import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsBestResponse
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe

/-!
# IsNashEquilibrium

Topic: equilibria   Node: 86b3bc8a3c86

Provenance: formalization of a published result. Source: EconCSLib, `IsNashEquilibrium`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/NashEquilibrium.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

A profile `σ` is a pure Nash equilibrium of game `G` if every player is playing a best response: no player can profitably deviate.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} [DecidableEq N] [Preorder U] in
open EconCSLib.StrategicGame in
/-- A profile `σ` is a pure Nash equilibrium of game `G` if every player is playing a best response: no player can profitably deviate. -/
def IsNashEquilibrium (G : EconCSLib.StrategicGame N U) (σ : G.Profile) : Prop :=
  ∀ i : N, IsBestResponse G σ i
