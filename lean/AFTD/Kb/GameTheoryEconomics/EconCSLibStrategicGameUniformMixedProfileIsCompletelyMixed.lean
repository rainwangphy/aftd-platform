import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameUniformMixedProfile
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsCompletelyMixedProfile
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameUniformMixedIsCompletelyMixed
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame

/-!
# EconCSLib.StrategicGame.uniformMixedProfile_isCompletelyMixed

Topic: equilibria   Node: 0c16a7704b54

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.uniformMixedProfile_isCompletelyMixed`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/MixedStrategy.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

The uniform mixed profile is completely mixed.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {N U : Type*} [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
/-- The uniform mixed profile is completely mixed. -/
theorem EconCSLib.StrategicGame.uniformMixedProfile_isCompletelyMixed
    (G : EconCSLib.StrategicGame N ℚ) [∀ i, Fintype (G.strategy i)]
    [∀ i, Nonempty (G.strategy i)] :
    IsCompletelyMixedProfile G (uniformMixedProfile G) := by
  intro i
  exact uniformMixed_isCompletelyMixed (G := G) (i := i)
