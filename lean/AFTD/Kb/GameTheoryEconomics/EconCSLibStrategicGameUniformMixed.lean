import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameMixedStrategy
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame

/-!
# EconCSLib.StrategicGame.uniformMixed

Topic: equilibria   Node: b05f3049562c

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.uniformMixed`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/MixedStrategy.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

The uniform mixed strategy over a finite nonempty strategy set.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {N U : Type*} [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
/-- The uniform mixed strategy over a finite nonempty strategy set. -/
def EconCSLib.StrategicGame.uniformMixed {G : EconCSLib.StrategicGame N U}
    {i : N} [Fintype (G.strategy i)] [Nonempty (G.strategy i)] :
    MixedStrategy G i where
  val _ := 1 / Fintype.card (G.strategy i)
  property := ⟨fun _ => by positivity,
               by simp [Finset.sum_const, Finset.card_univ]⟩
