import AFTD.Prelude
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisExtendDropColumn
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisSumSplitAt
import AFTD.Kb.Optimization.WsumPureApply

/-!
# MinimaxLoomis.wsum_extendDropColumn

Topic: equilibria   Node: 9272cc274966

Provenance: formalization of a published result. Source: EconCSLib, `MinimaxLoomis.wsum_extendDropColumn`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/MinimaxLoomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`wsum (extendDropColumn j₀ y') f` equals the `wsum` of `y'` restricted to the corresponding sub-function on `{j // j ≠ j₀}`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- `wsum (extendDropColumn j₀ y') f` equals the `wsum` of `y'` restricted to the corresponding sub-function on `{j // j ≠ j₀}`. -/
theorem MinimaxLoomis.wsum_extendDropColumn [DecidableEq J] (j₀ : J)
    (y' : stdSimplex ℝ {j : J // j ≠ j₀}) (f : J → ℝ) :
    wsum (extendDropColumn j₀ y') f
      = ∑ j' : {j : J // j ≠ j₀}, y'.val j' * f j'.val := by
  change (∑ j, (if h : j = j₀ then (0 : ℝ) else y'.val ⟨j, h⟩) * f j)
       = ∑ j' : {j : J // j ≠ j₀}, y'.val j' * f j'.val
  rw [sum_split_at j₀]
  have h0 : (if h : (j₀ : J) = j₀ then (0 : ℝ) else y'.val ⟨j₀, h⟩) * f j₀ = 0 := by
    have : (if h : (j₀ : J) = j₀ then (0 : ℝ) else y'.val ⟨j₀, h⟩) = 0 := by simp
    rw [this, zero_mul]
  rw [h0, zero_add]
  apply Finset.sum_congr rfl
  intro j' _
  congr 1
  simp [j'.property]
