import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGameOptimalRowStrategies
import AFTD.Kb.GameTheoryEconomics.MatrixGameValue
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstDecidableEqStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.Optimization.StdSimplexPure
import AFTD.Kb.GameTheoryEconomics.MatrixGameE
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.Optimization.WsumPureApply
import AFTD.Kb.Optimization.WsumWsumComm
import AFTD.Kb.Optimization.StdSimplexPureApply
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstNonemptyStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameOptimalRowSet
import AFTD.Kb.GameTheoryEconomics.MatrixGameMemOptimalRowStrategiesIffEGe
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstFintypeStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.Optimization.GeIffSimplexGe

/-!
# MatrixGame.image_optimalRowStrategies_eq

Topic: equilibria   Node: bfb512dce295

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.image_optimalRowStrategies_eq`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/OptimalStrategySetPolytope.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The image of the row-optimal subtype set equals the H-representation polytope `A.optimalRowSet`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Set in
set_option linter.unusedSectionVars false in
universe u in
variable {I J : Type u} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable (A : MatrixGame I J ℝ) in
/-- The image of the row-optimal subtype set equals the H-representation polytope `A.optimalRowSet`. -/
theorem MatrixGame.image_optimalRowStrategies_eq :
    (Subtype.val '' A.optimalRowStrategies) = A.optimalRowSet := by
  classical
  ext f
  constructor
  · rintro ⟨xx, hxx, rfl⟩
    refine ⟨xx.property, ?_⟩
    rw [mem_iInter]
    intro j
    have hpair := (A.mem_optimalRowStrategies_iff_E_ge xx).mp hxx (stdSimplex.pure j)
    have heq : A.E xx (stdSimplex.pure j) = ∑ i, xx.val i * A.g i j := by
      show wsum xx (fun i => wsum (stdSimplex.pure j) (A.g i)) = ∑ i, xx.val i * A.g i j
      apply Finset.sum_congr rfl
      intro i _
      show xx.val i * wsum (stdSimplex.pure j) (A.g i) = xx.val i * A.g i j
      rw [wsum_pure_apply]
    show A.value ≤ ∑ i, xx.val i * A.g i j
    rw [← heq]; exact hpair
  · rintro ⟨hf, hineq⟩
    refine ⟨⟨f, hf⟩, ?_, rfl⟩
    rw [mem_iInter] at hineq
    rw [A.mem_optimalRowStrategies_iff_E_ge ⟨f, hf⟩]
    intro y'
    have hEeq : A.E ⟨f, hf⟩ y' = wsum y' (fun j => ∑ i, f i * A.g i j) := by
      show wsum ⟨f, hf⟩ (fun i => wsum y' (A.g i)) = wsum y' (fun j => ∑ i, f i * A.g i j)
      have hcomm : wsum ⟨f, hf⟩ (fun i => wsum y' (A.g i))
                 = wsum y' (fun j => wsum ⟨f, hf⟩ (fun i => A.g i j)) :=
        wsum_wsum_comm ⟨f, hf⟩ y' A.g
      rw [hcomm]
      rfl
    rw [hEeq]
    have hbound : ∀ j, A.value ≤ ∑ i, f i * A.g i j := hineq
    exact (ge_iff_simplex_ge.mp hbound) y'
