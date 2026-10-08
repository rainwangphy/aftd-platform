import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameMixedStrategy
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame

/-!
# EconCSLib.StrategicGame.pureToMixed

Topic: equilibria   Node: 36befc756db3

Provenance: formalization of a published result. Source: EconCSLib, `StrategicGame.pureToMixed`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/MixedStrategy.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Embed a pure strategy as a mixed strategy (point mass).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {N U : Type*} [Field U] [LinearOrder U] [IsStrictOrderedRing U] in
/-- Embed a pure strategy as a mixed strategy (point mass). -/
def EconCSLib.StrategicGame.pureToMixed {G : EconCSLib.StrategicGame N U}
    {i : N} [Fintype (G.strategy i)] [DecidableEq (G.strategy i)]
    (s₀ : G.strategy i) : MixedStrategy G i where
  val s := if s = s₀ then 1 else 0
  property := ⟨fun s => by simp only; split_ifs <;> norm_num,
               by simp [Finset.sum_ite_eq', Finset.mem_univ]⟩
