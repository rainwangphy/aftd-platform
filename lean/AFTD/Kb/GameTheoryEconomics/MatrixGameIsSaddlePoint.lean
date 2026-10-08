import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameIsMixedNashEq

/-!
# MatrixGame.IsSaddlePoint

Topic: equilibria   Node: 9a1e7c3e74a3

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.IsSaddlePoint`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/MatrixGameNash.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A pair of mixed strategies is a **saddle point** when player I's payoff is maximised by the row strategy against the column strategy and minimised by the column strategy against the row strategy. For a matrix game this is synonymous with the mixed Nash equilibrium predicate [`MatrixGame.IsMixedNashEq`].
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
universe u in
variable {I J : Type u} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable (A : MatrixGame I J ℝ) in
/-- A pair of mixed strategies is a **saddle point** when player I's payoff is maximised by the row strategy against the column strategy and minimised by the column strategy against the row strategy. For a matrix game this is synonymous with the mixed Nash equilibrium predicate [`MatrixGame.IsMixedNashEq`]. -/
abbrev MatrixGame.IsSaddlePoint {𝕜 : Type} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (A : MatrixGame I J 𝕜) (xx : stdSimplex 𝕜 I) (yy : stdSimplex 𝕜 J) : Prop :=
  A.IsMixedNashEq xx yy
