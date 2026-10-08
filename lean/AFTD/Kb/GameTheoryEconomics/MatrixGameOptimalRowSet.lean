import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameValue
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstDecidableEqStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstFintypeStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstNonemptyStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.Tcs.G

/-!
# MatrixGame.optimalRowSet

Topic: equilibria   Node: dc9a4d857c6a

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.optimalRowSet`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/OptimalStrategySetPolytope.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

H-representation of the row-optimal strategy set in the ambient space `I → ℝ`: the standard simplex intersected with the finitely many half-spaces `A.value ≤ ∑ i, f i * A.g i j`, one per pure column `j`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Set in
set_option linter.unusedSectionVars false in
universe u in
variable {I J : Type u} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable (A : MatrixGame I J ℝ) in
/-- H-representation of the row-optimal strategy set in the ambient space `I → ℝ`: the standard simplex intersected with the finitely many half-spaces `A.value ≤ ∑ i, f i * A.g i j`, one per pure column `j`. -/
def MatrixGame.optimalRowSet : Set (I → ℝ) :=
  stdSimplex ℝ I ∩ ⋂ j : J, {f : I → ℝ | A.value ≤ ∑ i, f i * A.g i j}
