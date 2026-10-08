import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameOptimalColumnSet
import AFTD.Kb.GameTheoryEconomics.MatrixGameEj
import AFTD.Kb.GameTheoryEconomics.MatrixGameEi
import AFTD.Kb.GameTheoryEconomics.MatrixGameMinimaxOptimalStrategies
import AFTD.Kb.GameTheoryEconomics.MatrixGameValue
import AFTD.Kb.GameTheoryEconomics.MatrixGameMaximin
import AFTD.Kb.GameTheoryEconomics.MatrixGameGuaranteeI
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisLamAux
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisLamAuxBddAbove
import AFTD.Kb.GameTheoryEconomics.MatrixGameMinimax
import AFTD.Kb.GameTheoryEconomics.MatrixGameGuaranteeII
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisMuAux
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisMuAuxBddBelow
import AFTD.Kb.GameTheoryEconomics.MatrixGameMaximinLeMinimax
import AFTD.Kb.GameTheoryEconomics.MatrixGameValueEqMaximin
import AFTD.Kb.Optimization.WsumPureApply
import AFTD.Kb.GameTheoryEconomics.MatrixGameToMixedProfileZero
import AFTD.Kb.GameTheoryEconomics.MatrixGameToMixedProfileOne
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstDecidableEqStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstFintypeStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstNonemptyStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.Tcs.G
import AFTD.Kb.GameTheoryEconomics.LoomisLamBAuxBddAbove
import AFTD.Kb.GameTheoryEconomics.LoomisMuBAuxBddBelow

/-!
# MatrixGame.optimalColumnSet_nonempty

Topic: equilibria   Node: f8e63e92f7c4

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.optimalColumnSet_nonempty`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/OptimalStrategySetPolytope.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

MatrixGame.optimalColumnSet_nonempty
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MatrixGame in
open Finset BigOperators Set in
set_option linter.unusedSectionVars false in
universe u in
variable {I J : Type u} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable (A : MatrixGame I J ℝ) in
theorem MatrixGame.optimalColumnSet_nonempty : A.optimalColumnSet.Nonempty := by
  obtain ⟨xx, yy, v, Hxx, Hyy⟩ := A.minimax_optimal_strategies
  refine ⟨yy.val, yy.property, ?_⟩
  rw [mem_iInter]
  intro i
  have hv : v = A.value := by
    have h_le : v ≤ A.maximin := by
      have hxx_guarantee : v ≤ A.guarantee_I xx := by
        show v ≤ Finset.inf' Finset.univ Finset.univ_nonempty (fun j => A.Ej xx j)
        rw [Finset.le_inf'_iff]; intro j _; exact Hxx j
      have hg_le : A.guarantee_I xx ≤ A.maximin :=
        le_ciSup (bddAbove_def.2 (by
          obtain ⟨C, hC⟩ := MinimaxLoomis.lam.aux.bddAbove A.g
          exact ⟨C, by rintro r ⟨z, rfl⟩; exact hC z⟩)) xx
      linarith
    have h_ge_min : A.minimax ≤ v := by
      have hyy_guarantee : A.guarantee_II yy ≤ v := by
        show Finset.sup' Finset.univ Finset.univ_nonempty (fun i => A.Ei i yy) ≤ v
        rw [Finset.sup'_le_iff]; intro i _; exact Hyy i
      have hg_ge : A.minimax ≤ A.guarantee_II yy := by
        have hbb : BddBelow (Set.range (A.guarantee_II)) := by
          obtain ⟨C, hC⟩ := MinimaxLoomis.mu.aux.bddBelow A.g
          exact ⟨C, by rintro r ⟨z, rfl⟩; exact hC z⟩
        exact ciInf_le hbb yy
      linarith
    have hmm : A.maximin ≤ A.minimax := A.maximin_le_minimax
    have : v = A.maximin := by linarith
    rw [this, ← A.value_eq_maximin]
  show ∑ j, yy.val j * A.g i j ≤ A.value
  have h1 : A.Ei i yy ≤ A.value := by rw [← hv]; exact Hyy i
  exact h1
