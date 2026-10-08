import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameDeviate
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe

/-!
# isNashEq

Topic: equilibria   Node: d4825b25020d

Provenance: formalization of a published result. Source: EconCSLib, `isNashEq`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/Checker.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Executable Nash equilibrium checker. Returns `true` iff `σ` is a pure Nash equilibrium of `G`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} [DecidableEq N] [Preorder U] [DecidableRel (· ≤ · : U → U → Prop)] in
open EconCSLib.StrategicGame in
/-- Executable Nash equilibrium checker. Returns `true` iff `σ` is a pure Nash equilibrium of `G`. -/
def isNashEq [Fintype N] (G : EconCSLib.StrategicGame N U) [∀ i, Fintype (G.strategy i)]
    (σ : G.Profile) : Bool :=
  decide (∀ i : N, ∀ s' : G.strategy i, G.payoff (EconCSLib.StrategicGame.deviate σ i s') i ≤ G.payoff σ i)
