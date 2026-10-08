import AFTD.Prelude

/-!
# linear_comb_gt_of_ge_gt

Topic: lp_duality   Node: ff5c658c85e6

Provenance: formalization of a published result. Source: EconCSLib, `linear_comb_gt_of_ge_gt`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Simplex.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Convex combination of "≥ c" and "> c" stays "> c" (provided `α ≥ 0` and `α < 1`).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] in
set_option linter.unusedSectionVars false in
/-- Convex combination of "≥ c" and "> c" stays "> c" (provided `α ≥ 0` and `α < 1`). -/
theorem linear_comb_gt_of_ge_gt (x y c : 𝕜) (H1 : c ≤ x) (H2 : c < y)
    {α : 𝕜} (hα₀ : 0 ≤ α) (hα₁ : α < 1) :
    c < α * x + (1 - α) * y := by
  have hpos : 0 < 1 - α := by linarith
  have hxc : 0 ≤ α * (x - c) := mul_nonneg hα₀ (by linarith)
  have hyc : 0 < (1 - α) * (y - c) := mul_pos hpos (by linarith)
  nlinarith
