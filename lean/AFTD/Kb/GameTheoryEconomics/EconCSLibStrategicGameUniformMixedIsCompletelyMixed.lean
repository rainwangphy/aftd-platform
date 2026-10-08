import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameUniformMixedPos
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameUniformMixed
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsCompletelyMixed

/-!
# EconCSLib.StrategicGame.uniformMixed_isCompletelyMixed

Topic: equilibria   Node: a8461e8768fd

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.uniformMixed_isCompletelyMixed`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/MixedStrategy.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

The uniform mixed strategy is completely mixed on any finite nonempty strategy set.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {N U : Type*} [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
/-- The uniform mixed strategy is completely mixed on any finite nonempty strategy set. -/
theorem EconCSLib.StrategicGame.uniformMixed_isCompletelyMixed {G : EconCSLib.StrategicGame N ℚ}
    {i : N} [Fintype (G.strategy i)] [Nonempty (G.strategy i)] :
    IsCompletelyMixed G (uniformMixed (G := G) (i := i)) := by
  intro s
  exact uniformMixed_pos (G := G) (i := i) s
