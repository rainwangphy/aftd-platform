import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGameMemOptimalColumnStrategiesIffELe
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameOptimalRowStrategies
import AFTD.Kb.GameTheoryEconomics.MatrixGameOptimalColumnStrategies
import AFTD.Kb.GameTheoryEconomics.MatrixGameEj
import AFTD.Kb.GameTheoryEconomics.MatrixGameValue
import AFTD.Kb.GameTheoryEconomics.MatrixGameE
import AFTD.Kb.GameTheoryEconomics.MatrixGameMemOptimalRowStrategiesIffEGe
import AFTD.Kb.Optimization.StdSimplexPure
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.Optimization.WsumPureApply
import AFTD.Kb.Optimization.WsumWsumComm
import AFTD.Kb.Optimization.StdSimplexPureApply

/-!
# MatrixGame.support_complementarity_column

Topic: equilibria   Node: 61907e2f5040

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.support_complementarity_column`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/MatrixGameNash.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Support complementarity (column).** For an optimal pair `(xx, yy)`, every column `j` with positive probability under `yy` is a best response to `xx`, i.e., `A.Ej xx j = A.value`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MatrixGame in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
universe u in
variable {I J : Type u} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable (A : MatrixGame I J ℝ) in
/-- **Support complementarity (column).** For an optimal pair `(xx, yy)`, every column `j` with positive probability under `yy` is a best response to `xx`, i.e., `A.Ej xx j = A.value`. -/
theorem MatrixGame.support_complementarity_column [DecidableEq J]
    (xx : stdSimplex ℝ I) (yy : stdSimplex ℝ J)
    (hxx : xx ∈ A.optimalRowStrategies) (hyy : yy ∈ A.optimalColumnStrategies)
    {j : J} (hj : 0 < yy.val j) :
    A.Ej xx j = A.value := by
  have hE_eq : A.E xx yy = A.value := by
    have h1 := (A.mem_optimalRowStrategies_iff_E_ge xx).mp hxx yy
    have h2 := (A.mem_optimalColumnStrategies_iff_E_le yy).mp hyy xx
    linarith
  have hj_ge : ∀ j', A.value ≤ A.Ej xx j' := by
    intro j'
    have h := (A.mem_optimalRowStrategies_iff_E_ge xx).mp hxx (stdSimplex.pure j')
    have heq : A.E xx (stdSimplex.pure j') = A.Ej xx j' := by
      show wsum xx (fun i => wsum (stdSimplex.pure j') (A.g i)) = wsum xx (fun i => A.g i j')
      apply Finset.sum_congr rfl
      intro i _
      show xx.val i * wsum (stdSimplex.pure j') (A.g i) = xx.val i * A.g i j'
      rw [wsum_pure_apply]
    linarith [heq]
  -- Express E xx yy as a column-side weighted sum: ∑ j, yy.val j * Ej xx j.
  have hE_col : A.E xx yy = ∑ j', yy.val j' * A.Ej xx j' := by
    show wsum xx (fun i => wsum yy (A.g i)) = ∑ j', yy.val j' * (wsum xx (fun i => A.g i j'))
    rw [wsum_wsum_comm xx yy A.g]
    rfl
  have hsum_one : (∑ j', yy.val j') = 1 := yy.property.2
  have hsum_zero : (∑ j', yy.val j' * (A.Ej xx j' - A.value)) = 0 := by
    have hexpand : (∑ j', yy.val j' * (A.Ej xx j' - A.value))
        = (∑ j', yy.val j' * A.Ej xx j') - (∑ j', yy.val j') * A.value := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro j' _; ring
    rw [hexpand, hsum_one, one_mul, ← hE_col]
    linarith
  have hnonneg : ∀ j' ∈ Finset.univ, 0 ≤ yy.val j' * (A.Ej xx j' - A.value) := by
    intro j' _
    exact mul_nonneg (yy.property.1 j') (sub_nonneg.mpr (hj_ge j'))
  have hzero : yy.val j * (A.Ej xx j - A.value) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum_zero j (Finset.mem_univ j)
  rcases mul_eq_zero.mp hzero with h | h
  · linarith
  · linarith
