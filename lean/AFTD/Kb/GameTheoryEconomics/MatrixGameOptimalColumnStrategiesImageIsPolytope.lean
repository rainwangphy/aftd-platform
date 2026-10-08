import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameOptimalColumnStrategies
import AFTD.Kb.GameTheoryEconomics.MatrixGameOptimalColumnSet
import AFTD.Kb.GameTheoryEconomics.MatrixGameImageOptimalColumnStrategiesEq
import AFTD.Kb.GameTheoryEconomics.MatrixGameOptimalColumnSetConvex
import AFTD.Kb.GameTheoryEconomics.MatrixGameOptimalColumnSetIsClosed
import AFTD.Kb.GameTheoryEconomics.MatrixGameOptimalColumnSetIsCompact
import AFTD.Kb.GameTheoryEconomics.MatrixGameOptimalColumnSetNonempty
import AFTD.Kb.GameTheoryEconomics.MatrixGameToMixedProfileZero
import AFTD.Kb.GameTheoryEconomics.MatrixGameToMixedProfileOne
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstDecidableEqStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstFintypeStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstNonemptyStrategyFinOfNatNatToStrategicGame

/-!
# MatrixGame.optimalColumnStrategies_image_isPolytope

Topic: equilibria   Node: 10fa594d96a3

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.optimalColumnStrategies_image_isPolytope`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/OptimalStrategySetPolytope.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

MatrixGame.optimalColumnStrategies_image_isPolytope
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MatrixGame in
open Finset BigOperators Set in
set_option linter.unusedSectionVars false in
universe u in
variable {I J : Type u} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable (A : MatrixGame I J ℝ) in
theorem MatrixGame.optimalColumnStrategies_image_isPolytope :
    Convex ℝ (Subtype.val '' A.optimalColumnStrategies) ∧
    IsClosed (Subtype.val '' A.optimalColumnStrategies) ∧
    IsCompact (Subtype.val '' A.optimalColumnStrategies) ∧
    (Subtype.val '' A.optimalColumnStrategies).Nonempty := by
  rw [A.image_optimalColumnStrategies_eq]
  exact ⟨A.optimalColumnSet_convex, A.optimalColumnSet_isClosed,
         A.optimalColumnSet_isCompact, A.optimalColumnSet_nonempty⟩
