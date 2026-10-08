import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.StrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame

/-!
# EconCSLib.StrategicGame.uniformDist

Topic: equilibria   Node: 925c72190e18

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.StrategicGame.uniformDist`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/StochasticMatrix.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Uniform mixed strategy on a finite nonempty index type.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I : Type} [Fintype I] [Nonempty I] [DecidableEq I] in
/-- Uniform mixed strategy on a finite nonempty index type. -/
noncomputable def EconCSLib.StrategicGame.uniformDist : stdSimplex ℝ I :=
  ⟨fun _ => (1 : ℝ) / (Fintype.card I : ℝ),
    fun _ => by
      have : (0 : ℝ) ≤ (Fintype.card I : ℝ) := by exact_mod_cast Nat.zero_le _
      exact div_nonneg (by norm_num) this,
    by
      have hcard_pos : 0 < (Fintype.card I : ℝ) := by
        exact_mod_cast Fintype.card_pos
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp⟩
