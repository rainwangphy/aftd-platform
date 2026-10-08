import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameOptimalColumnSet
import AFTD.Kb.GameTheoryEconomics.MatrixGameValue
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstDecidableEqStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstFintypeStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstNonemptyStrategyFinOfNatNatToStrategicGame

/-!
# MatrixGame.optimalColumnSet_isClosed

Topic: equilibria   Node: 63196c076ba9

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.optimalColumnSet_isClosed`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/OptimalStrategySetPolytope.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

MatrixGame.optimalColumnSet_isClosed
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Set in
set_option linter.unusedSectionVars false in
universe u in
variable {I J : Type u} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable (A : MatrixGame I J ℝ) in
theorem MatrixGame.optimalColumnSet_isClosed : IsClosed A.optimalColumnSet := by
  have hsimplex : IsClosed (stdSimplex ℝ J) := isClosed_stdSimplex ℝ J
  apply IsClosed.inter hsimplex
  apply isClosed_iInter
  intro i
  exact IsClosed.preimage
    (continuous_finset_sum _ (fun j _ => (continuous_apply j).mul continuous_const))
    isClosed_Iic
