import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameMixedStrategy
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame

/-!
# EconCSLib.StrategicGame.MixedProfile

Topic: equilibria   Node: f6639e792f58

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.MixedProfile`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/MixedStrategy.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

A mixed profile: each player has a mixed strategy. No finiteness constraint on `N` (player set can be arbitrary).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {N U : Type*} [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
/-- A mixed profile: each player has a mixed strategy. No finiteness constraint on `N` (player set can be arbitrary). -/
def EconCSLib.StrategicGame.MixedProfile (G : EconCSLib.StrategicGame N U) [∀ i, Fintype (G.strategy i)] :=
  ∀ i, MixedStrategy G i
