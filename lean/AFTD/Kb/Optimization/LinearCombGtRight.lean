import AFTD.Prelude

/-!
# linear_comb_gt_right

Topic: lp_duality   Node: e6becbbaed6a

Provenance: formalization of a published result. Source: EconCSLib, `linear_comb_gt_right`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Simplex.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If `y < x` and `0 < α`, then `α·x + (1-α)·y > y`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] in
set_option linter.unusedSectionVars false in
/-- If `y < x` and `0 < α`, then `α·x + (1-α)·y > y`. -/
theorem linear_comb_gt_right {x y : 𝕜} (H : y < x) {α : 𝕜} (Hα : 0 < α) :
    y < α * x + (1 - α) * y := by
  have : 0 < α * (x - y) := mul_pos Hα (by linarith)
  nlinarith
