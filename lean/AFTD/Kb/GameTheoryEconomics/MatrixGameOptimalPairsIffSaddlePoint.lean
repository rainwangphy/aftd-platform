import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameOptimalRowStrategies
import AFTD.Kb.GameTheoryEconomics.MatrixGameOptimalColumnStrategies
import AFTD.Kb.GameTheoryEconomics.MatrixGameIsSaddlePoint
import AFTD.Kb.GameTheoryEconomics.MatrixGameValue
import AFTD.Kb.GameTheoryEconomics.MatrixGameE
import AFTD.Kb.GameTheoryEconomics.MatrixGameMemOptimalRowStrategiesIffEGe
import AFTD.Kb.GameTheoryEconomics.MatrixGameMemOptimalColumnStrategiesIffELe
import AFTD.Kb.GameTheoryEconomics.MatrixGameEj
import AFTD.Kb.Optimization.StdSimplexPure
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.Optimization.WsumPureApply
import AFTD.Kb.GameTheoryEconomics.MatrixGameEi
import AFTD.Kb.GameTheoryEconomics.MatrixGameGuaranteeI
import AFTD.Kb.GameTheoryEconomics.MatrixGameGuaranteeII
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisLamAux
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisLamAuxBddAbove
import AFTD.Kb.GameTheoryEconomics.MatrixGameMinimax
import AFTD.Kb.GameTheoryEconomics.MatrixGameValueEqMinimax
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisMuAux
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisMuAuxBddBelow
import AFTD.Kb.Optimization.StdSimplexPureApply
import AFTD.Kb.Tcs.G
import AFTD.Kb.GameTheoryEconomics.LoomisLamBAuxBddAbove
import AFTD.Kb.GameTheoryEconomics.LoomisMuBAuxBddBelow
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisE

/-!
# MatrixGame.optimal_pairs_iff_saddle_point

Topic: equilibria   Node: 021e0dd6e6f6

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.optimal_pairs_iff_saddle_point`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/MatrixGameNash.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Optimal pairs ↔ saddle points.** A pair of mixed strategies is in the product `X(A) × Y(A)` of optimal strategy sets iff it is a saddle point.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MatrixGame in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
universe u in
variable {I J : Type u} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable (A : MatrixGame I J ℝ) in
/-- **Optimal pairs ↔ saddle points.** A pair of mixed strategies is in the product `X(A) × Y(A)` of optimal strategy sets iff it is a saddle point. -/
theorem MatrixGame.optimal_pairs_iff_saddle_point
    (xx : stdSimplex ℝ I) (yy : stdSimplex ℝ J) :
    (xx ∈ A.optimalRowStrategies ∧ yy ∈ A.optimalColumnStrategies)
      ↔ A.IsSaddlePoint xx yy := by
  rw [A.mem_optimalRowStrategies_iff_E_ge, A.mem_optimalColumnStrategies_iff_E_le]
  refine ⟨?_, ?_⟩
  · rintro ⟨hxx, hyy⟩
    have hE : A.E xx yy = A.value := le_antisymm (hyy xx) (hxx yy)
    refine ⟨fun x' => ?_, fun y' => ?_⟩
    · calc A.E x' yy ≤ A.value := hyy x'
        _ = A.E xx yy := hE.symm
    · calc A.E xx yy = A.value := hE
        _ ≤ A.E xx y' := hxx y'
  · rintro ⟨hsad_row, hsad_col⟩
    classical
    have hjE : ∀ j, A.E xx yy ≤ A.Ej xx j := by
      intro j
      have := hsad_col (stdSimplex.pure j)
      have heq : A.E xx (stdSimplex.pure j) = A.Ej xx j := by
        show wsum xx (fun i => wsum (stdSimplex.pure j) (A.g i)) = wsum xx (fun i => A.g i j)
        apply Finset.sum_congr rfl
        intro i _
        show xx.val i * wsum (stdSimplex.pure j) (A.g i) = xx.val i * A.g i j
        rw [wsum_pure_apply]
      linarith [heq]
    have hiE : ∀ i, A.Ei i yy ≤ A.E xx yy := by
      intro i
      have := hsad_row (stdSimplex.pure i)
      have heq : A.E (stdSimplex.pure i) yy = A.Ei i yy := by
        show wsum (stdSimplex.pure i) (fun i' => wsum yy (A.g i')) = wsum yy (A.g i)
        rw [wsum_pure_apply]
      linarith [heq]
    have hGI : A.E xx yy ≤ A.guarantee_I xx := by
      show A.E xx yy ≤ Finset.inf' Finset.univ Finset.univ_nonempty (fun j => A.Ej xx j)
      rw [Finset.le_inf'_iff]; intro j _; exact hjE j
    have hGII : A.guarantee_II yy ≤ A.E xx yy := by
      show Finset.sup' Finset.univ Finset.univ_nonempty (fun i => A.Ei i yy) ≤ A.E xx yy
      rw [Finset.sup'_le_iff]; intro i _; exact hiE i
    have hI_le : A.guarantee_I xx ≤ A.value :=
      le_ciSup (bddAbove_def.2 (by
        obtain ⟨C, hC⟩ := MinimaxLoomis.lam.aux.bddAbove A.g
        exact ⟨C, by rintro r ⟨z, rfl⟩; exact hC z⟩)) xx
    have hII_ge : A.value ≤ A.guarantee_II yy := by
      have hv := A.value_eq_minimax
      have : A.minimax ≤ A.guarantee_II yy :=
        ciInf_le (bddBelow_def.2 (by
          obtain ⟨C, hC⟩ := MinimaxLoomis.mu.aux.bddBelow A.g
          exact ⟨C, by rintro r ⟨z, rfl⟩; exact hC z⟩)) yy
      linarith
    refine ⟨fun y' => ?_, fun x' => ?_⟩
    · have hEval : A.E xx yy = A.value := by linarith
      calc A.value = A.E xx yy := hEval.symm
        _ ≤ A.E xx y' := hsad_col y'
    · have hEval : A.E xx yy = A.value := by linarith
      calc A.E x' yy ≤ A.E xx yy := hsad_row x'
        _ = A.value := hEval
