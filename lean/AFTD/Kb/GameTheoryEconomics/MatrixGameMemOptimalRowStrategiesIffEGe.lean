import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGameOptimalRowStrategies
import AFTD.Kb.GameTheoryEconomics.MatrixGameValue
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisLamAuxBddAbove
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisLamAux
import AFTD.Kb.Optimization.StdSimplexPure
import AFTD.Kb.GameTheoryEconomics.MatrixGameE
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameValueEqMaximin
import AFTD.Kb.GameTheoryEconomics.MatrixGameGuaranteeI
import AFTD.Kb.Optimization.WsumPureApply
import AFTD.Kb.GameTheoryEconomics.MatrixGameMaximin
import AFTD.Kb.Optimization.WsumWsumComm
import AFTD.Kb.Optimization.StdSimplexPureApply
import AFTD.Kb.GameTheoryEconomics.MatrixGameEj
import AFTD.Kb.Optimization.GeIffSimplexGe

/-!
# MatrixGame.mem_optimalRowStrategies_iff_E_ge

Topic: equilibria   Node: e7601363a497

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.mem_optimalRowStrategies_iff_E_ge`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/MatrixGameNash.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A row strategy is optimal iff against every mixed column it secures the value.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
universe u in
variable {I J : Type u} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable (A : MatrixGame I J ℝ) in
/-- A row strategy is optimal iff against every mixed column it secures the value. -/
theorem MatrixGame.mem_optimalRowStrategies_iff_E_ge (xx : stdSimplex ℝ I) :
    xx ∈ A.optimalRowStrategies ↔ ∀ y' : stdSimplex ℝ J, A.value ≤ A.E xx y' := by
  classical
  unfold optimalRowStrategies
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hxx y'
    have hj : ∀ j, A.value ≤ A.Ej xx j := by
      intro j
      have : A.guarantee_I xx ≤ A.Ej xx j :=
        Finset.inf'_le (fun j => A.Ej xx j) (Finset.mem_univ j)
      linarith [hxx]
    have heq : A.E xx y' = wsum y' (fun j => A.Ej xx j) := by
      show wsum xx (fun i => wsum y' (A.g i)) = wsum y' (fun j => wsum xx (fun i => A.g i j))
      exact wsum_wsum_comm xx y' A.g
    rw [heq]
    exact (ge_iff_simplex_ge.mp hj) y'
  · intro h
    have hj : ∀ j, A.value ≤ A.Ej xx j := by
      intro j
      have := h (stdSimplex.pure j)
      have heq : A.E xx (stdSimplex.pure j) = A.Ej xx j := by
        show wsum xx (fun i => wsum (stdSimplex.pure j) (A.g i)) = wsum xx (fun i => A.g i j)
        apply Finset.sum_congr rfl
        intro i _
        show xx.val i * wsum (stdSimplex.pure j) (A.g i) = xx.val i * A.g i j
        rw [wsum_pure_apply]
      rwa [heq] at this
    have hge : A.value ≤ A.guarantee_I xx := by
      show A.value ≤ Finset.inf' Finset.univ Finset.univ_nonempty (fun j => A.Ej xx j)
      rw [Finset.le_inf'_iff]; intro j _; exact hj j
    have hle : A.guarantee_I xx ≤ A.value := by
      have hmax : A.guarantee_I xx ≤ A.maximin :=
        le_ciSup (bddAbove_def.2 (by
          obtain ⟨C, hC⟩ := MinimaxLoomis.lam.aux.bddAbove A.g
          exact ⟨C, by rintro r ⟨z, rfl⟩; exact hC z⟩)) xx
      have hv : A.value = A.maximin := A.value_eq_maximin
      linarith
    linarith
