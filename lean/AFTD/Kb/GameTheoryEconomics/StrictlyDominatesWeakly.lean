import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.WeaklyDominates
import AFTD.Kb.GameTheoryEconomics.StrictlyDominates
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameDeviate
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe

/-!
# StrictlyDominates.weakly

Topic: equilibria   Node: 6e7035f699da

Provenance: formalization of a published result. Source: EconCSLib, `StrictlyDominates.weakly`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/Dominance.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Strict dominance implies weak dominance.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} [DecidableEq N] [Preorder U] in
open EconCSLib.StrategicGame in
/-- Strict dominance implies weak dominance. -/
theorem StrictlyDominates.weakly {G : EconCSLib.StrategicGame N U} {i : N} {s s' : G.strategy i}
    (h : StrictlyDominates G i s s') : WeaklyDominates G i s s' :=
  fun σ => le_of_lt (h σ)
