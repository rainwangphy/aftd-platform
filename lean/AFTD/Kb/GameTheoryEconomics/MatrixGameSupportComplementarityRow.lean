import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameOptimalRowStrategies
import AFTD.Kb.GameTheoryEconomics.MatrixGameOptimalColumnStrategies
import AFTD.Kb.GameTheoryEconomics.MatrixGameEi
import AFTD.Kb.GameTheoryEconomics.MatrixGameValue
import AFTD.Kb.GameTheoryEconomics.MatrixGameE
import AFTD.Kb.GameTheoryEconomics.MatrixGameMemOptimalRowStrategiesIffEGe
import AFTD.Kb.GameTheoryEconomics.MatrixGameMemOptimalColumnStrategiesIffELe
import AFTD.Kb.Optimization.StdSimplexPure
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.Optimization.WsumPureApply
import AFTD.Kb.Optimization.StdSimplexPureApply
import AFTD.Kb.Tcs.G

/-!
# MatrixGame.support_complementarity_row

Topic: equilibria   Node: ea2dea3b9f2b

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.support_complementarity_row`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/MatrixGameNash.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Support complementarity (row).** For an optimal pair `(xx, yy)`, every row `i` with positive probability under `xx` is a best response to `yy`, i.e., `A.Ei i yy = A.value`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MatrixGame in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
universe u in
variable {I J : Type u} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable (A : MatrixGame I J ℝ) in
/-- **Support complementarity (row).** For an optimal pair `(xx, yy)`, every row `i` with positive probability under `xx` is a best response to `yy`, i.e., `A.Ei i yy = A.value`. -/
theorem MatrixGame.support_complementarity_row [DecidableEq I]
    (xx : stdSimplex ℝ I) (yy : stdSimplex ℝ J)
    (hxx : xx ∈ A.optimalRowStrategies) (hyy : yy ∈ A.optimalColumnStrategies)
    {i : I} (hi : 0 < xx.val i) :
    A.Ei i yy = A.value := by
  have hE_eq : A.E xx yy = A.value := by
    have h1 := (A.mem_optimalRowStrategies_iff_E_ge xx).mp hxx yy
    have h2 := (A.mem_optimalColumnStrategies_iff_E_le yy).mp hyy xx
    linarith
  have hi_le : ∀ i', A.Ei i' yy ≤ A.value := by
    intro i'
    have h := (A.mem_optimalColumnStrategies_iff_E_le yy).mp hyy (stdSimplex.pure i')
    have heq : A.E (stdSimplex.pure i') yy = A.Ei i' yy := by
      show wsum (stdSimplex.pure i') (fun i'' => wsum yy (A.g i'')) = wsum yy (A.g i')
      rw [wsum_pure_apply]
    linarith [heq]
  have hsum_one : (∑ i', xx.val i') = 1 := xx.property.2
  have hsum_zero : (∑ i', xx.val i' * (A.value - A.Ei i' yy)) = 0 := by
    have hexpand : (∑ i', xx.val i' * (A.value - A.Ei i' yy))
        = (∑ i', xx.val i') * A.value - (∑ i', xx.val i' * A.Ei i' yy) := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro i' _; ring
    rw [hexpand, hsum_one, one_mul]
    show A.value - A.E xx yy = 0
    linarith
  have hnonneg : ∀ i' ∈ Finset.univ, 0 ≤ xx.val i' * (A.value - A.Ei i' yy) := by
    intro i' _
    exact mul_nonneg (xx.property.1 i') (sub_nonneg.mpr (hi_le i'))
  have hzero : xx.val i * (A.value - A.Ei i yy) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum_zero i (Finset.mem_univ i)
  rcases mul_eq_zero.mp hzero with h | h
  · linarith
  · linarith
