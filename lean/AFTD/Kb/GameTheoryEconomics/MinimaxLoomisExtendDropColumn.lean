import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisSumSplitAt

/-!
# MinimaxLoomis.extendDropColumn

Topic: equilibria   Node: 1f0991078dac

Provenance: formalization of a published result. Source: EconCSLib, `MinimaxLoomis.extendDropColumn`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/MinimaxLoomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Extend a mixed strategy on `J' = {j // j ≠ j₀}` to a mixed strategy on `J` by putting zero mass on `j₀`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- Extend a mixed strategy on `J' = {j // j ≠ j₀}` to a mixed strategy on `J` by putting zero mass on `j₀`. -/
noncomputable def MinimaxLoomis.extendDropColumn [DecidableEq J] (j₀ : J)
    (y' : stdSimplex ℝ {j : J // j ≠ j₀}) :
    stdSimplex ℝ J := by
  refine ⟨fun j => if h : j = j₀ then 0 else y'.val ⟨j, h⟩, ?_, ?_⟩
  · intro j
    by_cases h : j = j₀
    · simp [h]
    · simp [h]; exact y'.property.1 ⟨j, h⟩
  · rw [sum_split_at j₀]
    have h0 : (if h : (j₀ : J) = j₀ then (0 : ℝ) else y'.val ⟨j₀, h⟩) = 0 := by simp
    rw [h0, zero_add]
    have : ∀ j' : {j : J // j ≠ j₀},
        (if h : j'.val = j₀ then (0 : ℝ) else y'.val ⟨j'.val, h⟩) = y'.val j' := by
      intro j'; simp [j'.property]
    simp_rw [this]
    exact y'.property.2
