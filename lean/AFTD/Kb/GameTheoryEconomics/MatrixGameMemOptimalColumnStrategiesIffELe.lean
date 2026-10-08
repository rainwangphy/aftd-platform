import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGameValueEqMinimax
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameOptimalColumnStrategies
import AFTD.Kb.GameTheoryEconomics.MatrixGameE
import AFTD.Kb.GameTheoryEconomics.MatrixGameValue
import AFTD.Kb.GameTheoryEconomics.MatrixGameGuaranteeII
import AFTD.Kb.GameTheoryEconomics.MatrixGameEi
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.Optimization.LeIffSimplexLe
import AFTD.Kb.Optimization.StdSimplexPure
import AFTD.Kb.Optimization.WsumPureApply
import AFTD.Kb.GameTheoryEconomics.MatrixGameMinimax
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisMuAux
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisMuAuxBddBelow
import AFTD.Kb.Optimization.StdSimplexPureApply
import AFTD.Kb.GameTheoryEconomics.LoomisMuBAuxBddBelow

/-!
# MatrixGame.mem_optimalColumnStrategies_iff_E_le

Topic: equilibria   Node: 9ccc086a2051

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.mem_optimalColumnStrategies_iff_E_le`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/MatrixGameNash.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A column strategy is optimal iff against every mixed row it caps payoff at the value.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MatrixGame in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
universe u in
variable {I J : Type u} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable (A : MatrixGame I J ℝ) in
/-- A column strategy is optimal iff against every mixed row it caps payoff at the value. -/
theorem MatrixGame.mem_optimalColumnStrategies_iff_E_le (yy : stdSimplex ℝ J) :
    yy ∈ A.optimalColumnStrategies ↔ ∀ x' : stdSimplex ℝ I, A.E x' yy ≤ A.value := by
  classical
  unfold optimalColumnStrategies
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hyy x'
    have hi : ∀ i, A.Ei i yy ≤ A.value := by
      intro i
      have : A.Ei i yy ≤ A.guarantee_II yy :=
        Finset.le_sup' (fun i => A.Ei i yy) (Finset.mem_univ i)
      linarith [hyy]
    have heq : A.E x' yy = wsum x' (fun i => A.Ei i yy) := rfl
    rw [heq]
    exact (le_iff_simplex_le.mp hi) x'
  · intro h
    have hi : ∀ i, A.Ei i yy ≤ A.value := by
      intro i
      have := h (stdSimplex.pure i)
      have heq : A.E (stdSimplex.pure i) yy = A.Ei i yy := by
        show wsum (stdSimplex.pure i) (fun i' => wsum yy (A.g i')) = wsum yy (A.g i)
        rw [wsum_pure_apply]
      rwa [heq] at this
    have hle : A.guarantee_II yy ≤ A.value := by
      show Finset.sup' Finset.univ Finset.univ_nonempty (fun i => A.Ei i yy) ≤ A.value
      rw [Finset.sup'_le_iff]; intro i _; exact hi i
    have hge : A.value ≤ A.guarantee_II yy := by
      have hv := A.value_eq_minimax
      have : A.minimax ≤ A.guarantee_II yy :=
        ciInf_le (bddBelow_def.2 (by
          obtain ⟨C, hC⟩ := MinimaxLoomis.mu.aux.bddBelow A.g
          exact ⟨C, by rintro r ⟨z, rfl⟩; exact hC z⟩)) yy
      linarith
    linarith
