import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameToStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsZeroSumDecidable
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstDecidableEqStrategyFinOfNatNatToStrategicGame

/-!
# MatrixGame.instFintypeStrategyFinOfNatNatToStrategicGame

Topic: equilibria   Node: f98c7b94f62e

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.instFintypeStrategyFinOfNatNatToStrategicGame`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/MatrixGameNash.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

MatrixGame.instFintypeStrategyFinOfNatNatToStrategicGame
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
universe u in
variable {I J : Type u} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable (A : MatrixGame I J ℝ) in
instance MatrixGame.instFintypeStrategyFinOfNatNatToStrategicGame {𝕜 : Type} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (A : MatrixGame I J 𝕜) (i : Fin 2) :
    Fintype (A.toStrategicGame.strategy i) := by
  match i with
  | 0 => exact ‹Fintype I›
  | 1 => exact ‹Fintype J›
