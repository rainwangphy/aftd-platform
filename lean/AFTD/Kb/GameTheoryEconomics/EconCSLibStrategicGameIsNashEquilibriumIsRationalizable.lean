import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.GameTheoryEconomics.IsNashEquilibrium
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsRationalizable
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsNashEquilibriumSurvives
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe
import AFTD.Kb.GameTheoryEconomics.StrategicGame
import AFTD.Kb.GameTheoryEconomics.Profile

/-!
# EconCSLib.StrategicGame.IsNashEquilibrium.isRationalizable

Topic: equilibria   Node: b3e40bbe645f

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.IsNashEquilibrium.isRationalizable`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/IESDS.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Nash strategies are rationalizable.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open EconCSLib.StrategicGame in
variable {N U : Type*} [DecidableEq N] [Preorder U] in
open EconCSLib.StrategicGame in
/-- Nash strategies are rationalizable. -/
theorem EconCSLib.StrategicGame.IsNashEquilibrium.isRationalizable {G : EconCSLib.StrategicGame N U}
    {σ : G.Profile} (hN : IsNashEquilibrium G σ) (i : N) :
    G.IsRationalizable i (σ i) :=
  fun n => hN.survives n i
