import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsZeroSum
import AFTD.Kb.GameTheoryEconomics.MatrixGameToStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsZeroSumExpectedPayoffAddZero
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameIsZeroSumDecidable
import AFTD.Kb.GameTheoryEconomics.StrategicGame
import AFTD.Kb.Tcs.G

/-!
# MatrixGame.toStrategicGame_isZeroSum

Topic: equilibria   Node: 4072855f74ac

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.toStrategicGame_isZeroSum`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/MatrixGameNash.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

`A.toStrategicGame` satisfies the abstract zero-sum predicate: by construction player 1's payoff is the negation of player 0's.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
universe u in
variable {I J : Type u} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable (A : MatrixGame I J ℝ) in
/-- `A.toStrategicGame` satisfies the abstract zero-sum predicate: by construction player 1's payoff is the negation of player 0's. -/
theorem MatrixGame.toStrategicGame_isZeroSum {𝕜 : Type}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (A : MatrixGame I J 𝕜) :
    EconCSLib.StrategicGame.IsZeroSum A.toStrategicGame := by
  intro σ
  show A.g (σ 0) (σ 1) + -(A.g (σ 0) (σ 1)) = 0
  ring
