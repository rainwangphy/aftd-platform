import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameOptimalRowStrategies
import AFTD.Kb.GameTheoryEconomics.MatrixGameOptimalRowSet
import AFTD.Kb.GameTheoryEconomics.MatrixGameImageOptimalRowStrategiesEq
import AFTD.Kb.GameTheoryEconomics.MatrixGameOptimalRowSetConvex
import AFTD.Kb.GameTheoryEconomics.MatrixGameOptimalRowSetIsClosed
import AFTD.Kb.GameTheoryEconomics.MatrixGameOptimalRowSetIsCompact
import AFTD.Kb.GameTheoryEconomics.MatrixGameOptimalRowSetNonempty
import AFTD.Kb.GameTheoryEconomics.MatrixGameToMixedProfileZero
import AFTD.Kb.GameTheoryEconomics.MatrixGameToMixedProfileOne
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstDecidableEqStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstFintypeStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstNonemptyStrategyFinOfNatNatToStrategicGame

/-!
# MatrixGame.optimalRowStrategies_image_isPolytope

Topic: equilibria   Node: 66021877faa7

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.optimalRowStrategies_image_isPolytope`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/OptimalStrategySetPolytope.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The row-optimal strategy set is a nonempty polytope: convex, closed, compact, and nonempty.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MatrixGame in
open Finset BigOperators Set in
set_option linter.unusedSectionVars false in
universe u in
variable {I J : Type u} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable (A : MatrixGame I J ℝ) in
/-- The row-optimal strategy set is a nonempty polytope: convex, closed, compact, and nonempty. -/
theorem MatrixGame.optimalRowStrategies_image_isPolytope :
    Convex ℝ (Subtype.val '' A.optimalRowStrategies) ∧
    IsClosed (Subtype.val '' A.optimalRowStrategies) ∧
    IsCompact (Subtype.val '' A.optimalRowStrategies) ∧
    (Subtype.val '' A.optimalRowStrategies).Nonempty := by
  rw [A.image_optimalRowStrategies_eq]
  exact ⟨A.optimalRowSet_convex, A.optimalRowSet_isClosed,
         A.optimalRowSet_isCompact, A.optimalRowSet_nonempty⟩
