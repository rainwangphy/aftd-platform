import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameE

/-!
# MatrixGame.IsMixedNashEq

Topic: equilibria   Node: ba3123230a81

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.IsMixedNashEq`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/MatrixGameNash.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Saddle-point form of a mixed Nash equilibrium for a matrix game. For zero-sum two-player games, the standard mixed-strategy Nash equilibrium is exactly the saddle point of the bilinear payoff: the row player cannot improve by deviating to any mixed row, and the column player cannot improve (i.e., decrease the row player's payoff) by deviating to any mixed column. Field-generic: the saddle-point inequalities only need a linearly ordered field, not order-completeness.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
universe u in
variable {I J : Type u} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable (A : MatrixGame I J ℝ) in
/-- Saddle-point form of a mixed Nash equilibrium for a matrix game. For zero-sum two-player games, the standard mixed-strategy Nash equilibrium is exactly the saddle point of the bilinear payoff: the row player cannot improve by deviating to any mixed row, and the column player cannot improve (i.e., decrease the row player's payoff) by deviating to any mixed column. Field-generic: the saddle-point inequalities only need a linearly ordered field, not order-completeness. -/
def MatrixGame.IsMixedNashEq {𝕜 : Type} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (A : MatrixGame I J 𝕜) (xx : stdSimplex 𝕜 I) (yy : stdSimplex 𝕜 J) : Prop :=
  (∀ x' : stdSimplex 𝕜 I, A.E x' yy ≤ A.E xx yy) ∧
  (∀ y' : stdSimplex 𝕜 J, A.E xx yy ≤ A.E xx y')
