import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameGuaranteeII
import AFTD.Kb.GameTheoryEconomics.MatrixGameValue

/-!
# MatrixGame.IsEpsilonOptimalColumn

Topic: equilibria   Node: 6584596f99d8

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.IsEpsilonOptimalColumn`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/MatrixGameNash.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An **ε-optimal column strategy** caps player I's payoff at `value + ε`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
universe u in
variable {I J : Type u} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable (A : MatrixGame I J ℝ) in
/-- An **ε-optimal column strategy** caps player I's payoff at `value + ε`. -/
def MatrixGame.IsEpsilonOptimalColumn {𝕜 : Type} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜]
    (A : MatrixGame I J 𝕜) (ε : 𝕜) (yy : stdSimplex 𝕜 J) : Prop :=
  A.guarantee_II yy ≤ A.value + ε
