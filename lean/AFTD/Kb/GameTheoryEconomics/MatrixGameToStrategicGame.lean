import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsZeroSumDecidable
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.StrategicGame

/-!
# MatrixGame.toStrategicGame

Topic: equilibria   Node: 4278114b6e7a

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.toStrategicGame`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/MatrixGameNash.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

The two-player zero-sum strategic game associated with a matrix game. See `MatrixGame.toStrategicGame_isZeroSum` for the proof that this game satisfies the abstract `StrategicGame.IsZeroSum` predicate, so results stated against `IsZeroSum` (e.g. `IsZeroSum.nash_payoff_eq`) can be invoked on `A.toStrategicGame` without re-unfolding the definition.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
universe u in
variable {I J : Type u} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable (A : MatrixGame I J ℝ) in
/-- The two-player zero-sum strategic game associated with a matrix game. See `MatrixGame.toStrategicGame_isZeroSum` for the proof that this game satisfies the abstract `StrategicGame.IsZeroSum` predicate, so results stated against `IsZeroSum` (e.g. `IsZeroSum.nash_payoff_eq`) can be invoked on `A.toStrategicGame` without re-unfolding the definition. -/
noncomputable def MatrixGame.toStrategicGame {𝕜 : Type}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (A : MatrixGame I J 𝕜) : EconCSLib.StrategicGame (Fin 2) 𝕜 where
  strategy
  | 0 => I
  | 1 => J
  payoff σ
  | 0 => A.g (σ 0) (σ 1)
  | 1 => -(A.g (σ 0) (σ 1))
