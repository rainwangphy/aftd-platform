import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.StrategicGame
import AFTD.Kb.GameTheoryEconomics.MixedStrategy

/-!
# EconCSLib.StrategicGame.MixedStrategy

Topic: equilibria   Node: 02205309ed41

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.MixedStrategy`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/MixedStrategy.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

A mixed strategy for player `i`: a probability distribution over pure strategies. Requires `[Fintype (G.strategy i)]` but NOT `[Fintype N]`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {N U : Type*} [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
/-- A mixed strategy for player `i`: a probability distribution over pure strategies. Requires `[Fintype (G.strategy i)]` but NOT `[Fintype N]`. -/
abbrev EconCSLib.StrategicGame.MixedStrategy (G : EconCSLib.StrategicGame N U) (i : N) [Fintype (G.strategy i)] :=
  stdSimplex U (G.strategy i)
