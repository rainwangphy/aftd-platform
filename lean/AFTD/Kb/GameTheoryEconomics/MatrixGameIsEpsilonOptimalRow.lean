import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameValue
import AFTD.Kb.GameTheoryEconomics.MatrixGameGuaranteeI

/-!
# MatrixGame.IsEpsilonOptimalRow

Topic: equilibria   Node: d7a9b0b8d26f

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.IsEpsilonOptimalRow`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/MatrixGameNash.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An **ε-optimal row strategy** guarantees at least `value - ε`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
universe u in
variable {I J : Type u} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable (A : MatrixGame I J ℝ) in
/-- An **ε-optimal row strategy** guarantees at least `value - ε`. -/
def MatrixGame.IsEpsilonOptimalRow {𝕜 : Type} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜]
    (A : MatrixGame I J 𝕜) (ε : 𝕜) (xx : stdSimplex 𝕜 I) : Prop :=
  A.value - ε ≤ A.guarantee_I xx
