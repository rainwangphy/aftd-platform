import AFTD.Prelude

/-!
# linear_comb_gt_left

Topic: lp_duality   Node: e5ec3d63989a

Provenance: formalization of a published result. Source: EconCSLib, `linear_comb_gt_left`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Simplex.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If `x < y` and `α < 1`, then `α·x + (1-α)·y > x`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] in
set_option linter.unusedSectionVars false in
/-- If `x < y` and `α < 1`, then `α·x + (1-α)·y > x`. -/
theorem linear_comb_gt_left {x y : 𝕜} (H : x < y) {α : 𝕜} (Hα : α < 1) :
    x < α * x + (1 - α) * y := by
  have hpos : 0 < 1 - α := by linarith
  have : 0 < (1 - α) * (y - x) := mul_pos hpos (by linarith)
  nlinarith
