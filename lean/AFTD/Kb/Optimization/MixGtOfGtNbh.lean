import AFTD.Prelude

/-!
# mix_gt_of_gt_nbh

Topic: lp_duality   Node: 65054f2c86ab

Provenance: formalization of a published result. Source: EconCSLib, `mix_gt_of_gt_nbh`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Simplex.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Existence of a strictly interior `t` keeping `t·x + (1-t)·y > c`, given `c < x`. Constructive over any ordered field: pick `t` just above the crossing threshold `(c-y)/(x-y)` (clamped to `0`) when `y < x`, or any interior `t` when `x ≤ y`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] in
set_option linter.unusedSectionVars false in
/-- Existence of a strictly interior `t` keeping `t·x + (1-t)·y > c`, given `c < x`. Constructive over any ordered field: pick `t` just above the crossing threshold `(c-y)/(x-y)` (clamped to `0`) when `y < x`, or any interior `t` when `x ≤ y`. -/
theorem mix_gt_of_gt_nbh (x y c : 𝕜) (H : c < x) :
    ∃ t : 𝕜, 0 < t ∧ t < 1 ∧ c < t * x + (1 - t) * y := by
  rcases (lt_or_ge y x).symm with hxy | hyx
  · -- `x ≤ y`: the whole segment stays above `x > c`; any interior `t` works.
    refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
    have hexp : (1 / 2) * x + (1 - 1 / 2) * y = x + (1 / 2) * (y - x) := by ring
    rw [hexp]
    have : 0 ≤ (1 / 2 : 𝕜) * (y - x) := mul_nonneg (by norm_num) (by linarith)
    linarith
  · -- `y < x`: pick `t` above the crossing threshold but below `1`.
    have hd : 0 < x - y := by linarith
    have hthr_lt_one : (c - y) / (x - y) < 1 := (div_lt_one hd).mpr (by linarith)
    set a : 𝕜 := max ((c - y) / (x - y)) 0 with ha
    have ha_lt_one : a < 1 := max_lt hthr_lt_one one_pos
    have ha_nonneg : 0 ≤ a := le_max_right _ _
    have hthr_le_a : (c - y) / (x - y) ≤ a := le_max_left _ _
    refine ⟨(a + 1) / 2, by linarith, by linarith, ?_⟩
    have hthr_lt_t : (c - y) / (x - y) < (a + 1) / 2 := by linarith
    have hcy : c - y < ((a + 1) / 2) * (x - y) := (div_lt_iff₀ hd).mp hthr_lt_t
    have hexp : ((a + 1) / 2) * x + (1 - (a + 1) / 2) * y
        = y + ((a + 1) / 2) * (x - y) := by ring
    rw [hexp]; linarith
