import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameMixedStrategy
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameUniformMixed
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame

/-!
# EconCSLib.StrategicGame.uniformMixed_apply

Topic: equilibria   Node: a3dcaa54bda0

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.uniformMixed_apply`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/MixedStrategy.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

The uniform mixed strategy assigns `1 / card` to every pure strategy.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {N U : Type*} [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
/-- The uniform mixed strategy assigns `1 / card` to every pure strategy. -/
theorem EconCSLib.StrategicGame.uniformMixed_apply {G : EconCSLib.StrategicGame N ℚ}
    {i : N} [Fintype (G.strategy i)] [Nonempty (G.strategy i)]
    (s : G.strategy i) :
    (uniformMixed (G := G) (i := i)).val s = 1 / Fintype.card (G.strategy i) :=
  rfl
