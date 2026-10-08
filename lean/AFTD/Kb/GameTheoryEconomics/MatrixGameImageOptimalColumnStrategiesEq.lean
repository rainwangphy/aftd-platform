import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGameMemOptimalColumnStrategiesIffELe
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameOptimalColumnStrategies
import AFTD.Kb.GameTheoryEconomics.MatrixGameOptimalColumnSet
import AFTD.Kb.GameTheoryEconomics.MatrixGameValue
import AFTD.Kb.GameTheoryEconomics.MatrixGameE
import AFTD.Kb.Optimization.StdSimplexPure
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.Optimization.WsumPureApply
import AFTD.Kb.Optimization.LeIffSimplexLe
import AFTD.Kb.Optimization.StdSimplexPureApply
import AFTD.Kb.GameTheoryEconomics.MatrixGameToMixedProfileZero
import AFTD.Kb.GameTheoryEconomics.MatrixGameToMixedProfileOne
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstDecidableEqStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstFintypeStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstNonemptyStrategyFinOfNatNatToStrategicGame

/-!
# MatrixGame.image_optimalColumnStrategies_eq

Topic: equilibria   Node: 29b91eda9327

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.image_optimalColumnStrategies_eq`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/OptimalStrategySetPolytope.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

MatrixGame.image_optimalColumnStrategies_eq
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MatrixGame in
open Finset BigOperators Set in
set_option linter.unusedSectionVars false in
universe u in
variable {I J : Type u} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable (A : MatrixGame I J ℝ) in
theorem MatrixGame.image_optimalColumnStrategies_eq :
    (Subtype.val '' A.optimalColumnStrategies) = A.optimalColumnSet := by
  classical
  ext g
  constructor
  · rintro ⟨yy, hyy, rfl⟩
    refine ⟨yy.property, ?_⟩
    rw [mem_iInter]
    intro i
    have hpair := (A.mem_optimalColumnStrategies_iff_E_le yy).mp hyy (stdSimplex.pure i)
    have heq : A.E (stdSimplex.pure i) yy = ∑ j, yy.val j * A.g i j := by
      show wsum (stdSimplex.pure i) (fun i' => wsum yy (A.g i')) = ∑ j, yy.val j * A.g i j
      rw [wsum_pure_apply]
      rfl
    show ∑ j, yy.val j * A.g i j ≤ A.value
    rw [← heq]; exact hpair
  · rintro ⟨hg, hineq⟩
    refine ⟨⟨g, hg⟩, ?_, rfl⟩
    rw [mem_iInter] at hineq
    rw [A.mem_optimalColumnStrategies_iff_E_le ⟨g, hg⟩]
    intro x'
    have hEeq : A.E x' ⟨g, hg⟩ = wsum x' (fun i => ∑ j, g j * A.g i j) := rfl
    rw [hEeq]
    have hbound : ∀ i, ∑ j, g j * A.g i j ≤ A.value := hineq
    exact (le_iff_simplex_le.mp hbound) x'
