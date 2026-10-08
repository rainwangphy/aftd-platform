import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGameMinimaxTheorem
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameIsPlayerIGuarantee
import AFTD.Kb.GameTheoryEconomics.MatrixGameIsPlayerIIGuarantee
import AFTD.Kb.GameTheoryEconomics.MatrixGameValue
import AFTD.Kb.GameTheoryEconomics.MatrixGameEj
import AFTD.Kb.GameTheoryEconomics.MatrixGameEi
import AFTD.Kb.GameTheoryEconomics.MatrixGameGuaranteeI
import AFTD.Kb.GameTheoryEconomics.MatrixGameGuaranteeII
import AFTD.Kb.GameTheoryEconomics.MatrixGameMaximin
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisLamAux
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisLamAuxBddAbove
import AFTD.Kb.GameTheoryEconomics.MatrixGameMinimax
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisMuAux
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisMuAuxBddBelow
import AFTD.Kb.GameTheoryEconomics.MatrixGameValueEqMaximin
import AFTD.Kb.Optimization.WsumPureApply
import AFTD.Kb.GameTheoryEconomics.LoomisLamBAuxBddAbove
import AFTD.Kb.GameTheoryEconomics.LoomisMuBAuxBddBelow

/-!
# MatrixGame.common_guarantee_eq_value

Topic: equilibria   Node: 907a8708b012

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.common_guarantee_eq_value`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/MatrixGameNash.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Common guarantee gives the value.** If both players guarantee the same scalar `w`, then `w` equals the game value.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MatrixGame in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
universe u in
variable {I J : Type u} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable (A : MatrixGame I J ℝ) in
/-- **Common guarantee gives the value.** If both players guarantee the same scalar `w`, then `w` equals the game value. -/
theorem MatrixGame.common_guarantee_eq_value (w : ℝ)
    (h1 : A.IsPlayerIGuarantee w) (h2 : A.IsPlayerIIGuarantee w) :
    w = A.value := by
  obtain ⟨xx, hxx⟩ := h1
  obtain ⟨yy, hyy⟩ := h2
  have hw_le_GI : w ≤ A.guarantee_I xx := by
    show w ≤ Finset.inf' Finset.univ Finset.univ_nonempty (fun j => A.Ej xx j)
    rw [Finset.le_inf'_iff]; intro j _; exact hxx j
  have hGII_le_w : A.guarantee_II yy ≤ w := by
    show Finset.sup' Finset.univ Finset.univ_nonempty (fun i => A.Ei i yy) ≤ w
    rw [Finset.sup'_le_iff]; intro i _; exact hyy i
  have h_GI_max : A.guarantee_I xx ≤ A.maximin :=
    le_ciSup (bddAbove_def.2 (by
      obtain ⟨C, hC⟩ := MinimaxLoomis.lam.aux.bddAbove A.g
      exact ⟨C, by rintro r ⟨z, rfl⟩; exact hC z⟩)) xx
  have h_min_GII : A.minimax ≤ A.guarantee_II yy :=
    ciInf_le (bddBelow_def.2 (by
      obtain ⟨C, hC⟩ := MinimaxLoomis.mu.aux.bddBelow A.g
      exact ⟨C, by rintro r ⟨z, rfl⟩; exact hC z⟩)) yy
  have hvm := A.minimax_theorem
  have hvval := A.value_eq_maximin
  linarith
