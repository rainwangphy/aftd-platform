import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameSurvives
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe
import AFTD.Kb.GameTheoryEconomics.StrategicGame
import AFTD.Kb.GameTheoryEconomics.Profile

/-!
# EconCSLib.StrategicGame.IsDominanceSolvable

Topic: equilibria   Node: 15449c6d11a2

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.IsDominanceSolvable`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/IESDS.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

A game is dominance-solvable if IESDS yields a unique surviving profile.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} [DecidableEq N] [Preorder U] in
open EconCSLib.StrategicGame in
/-- A game is dominance-solvable if IESDS yields a unique surviving profile. -/
def EconCSLib.StrategicGame.IsDominanceSolvable (G : EconCSLib.StrategicGame N U) : Prop :=
  ∃! σ : G.Profile, ∀ i, ∀ n, G.Survives n i (σ i)
