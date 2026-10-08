import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGameValue
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstDecidableEqStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstNonemptyStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameOptimalRowSet
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstFintypeStrategyFinOfNatNatToStrategicGame

/-!
# MatrixGame.optimalRowSet_isClosed

Topic: equilibria   Node: 386149015506

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.optimalRowSet_isClosed`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/OptimalStrategySetPolytope.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

MatrixGame.optimalRowSet_isClosed
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Set in
set_option linter.unusedSectionVars false in
universe u in
variable {I J : Type u} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable (A : MatrixGame I J ℝ) in
theorem MatrixGame.optimalRowSet_isClosed : IsClosed A.optimalRowSet := by
  have hsimplex : IsClosed (stdSimplex ℝ I) := isClosed_stdSimplex ℝ I
  apply IsClosed.inter hsimplex
  apply isClosed_iInter
  intro j
  -- {f | A.value ≤ ∑ i, f i * A.g i j} is closed: preimage of [A.value, ∞)
  -- under the continuous functional f ↦ ∑ i, f i * A.g i j.
  refine IsClosed.preimage ?_ isClosed_Ici
  exact continuous_finset_sum _ (fun i _ => (continuous_apply i).mul continuous_const)
