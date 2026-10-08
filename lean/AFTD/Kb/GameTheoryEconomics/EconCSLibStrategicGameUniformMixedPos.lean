import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameMixedStrategy
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameUniformMixed
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameUniformMixedApply
import AFTD.Kb.GameTheoryEconomics.StrategicGame

/-!
# EconCSLib.StrategicGame.uniformMixed_pos

Topic: equilibria   Node: 4e38a8d6d2b8

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.uniformMixed_pos`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/MixedStrategy.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Every pure strategy has positive probability under the uniform mixed strategy.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {N U : Type*} [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
/-- Every pure strategy has positive probability under the uniform mixed strategy. -/
theorem EconCSLib.StrategicGame.uniformMixed_pos {G : EconCSLib.StrategicGame N ℚ}
    {i : N} [Fintype (G.strategy i)] [Nonempty (G.strategy i)]
    (s : G.strategy i) :
    0 < (uniformMixed (G := G) (i := i)).val s := by
  rw [uniformMixed_apply]
  exact one_div_pos.mpr (Nat.cast_pos.mpr (Fintype.card_pos (α := G.strategy i)))
