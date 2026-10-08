import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.StrictlyDominates
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe

/-!
# IsStrictlyDominant

Topic: equilibria   Node: d7ab95cf33b8

Provenance: formalization of a published result. Source: EconCSLib, `IsStrictlyDominant`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/Dominance.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Strategy `s` is strictly dominant for player `i`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} [DecidableEq N] [Preorder U] in
open EconCSLib.StrategicGame in
/-- Strategy `s` is strictly dominant for player `i`. -/
def IsStrictlyDominant (G : EconCSLib.StrategicGame N U) (i : N) (s : G.strategy i) : Prop :=
  ∀ s' : G.strategy i, s ≠ s' → StrictlyDominates G i s s'
