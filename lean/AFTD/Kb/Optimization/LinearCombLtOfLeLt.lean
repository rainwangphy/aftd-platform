import AFTD.Prelude

/-!
# linear_comb_lt_of_le_lt

Topic: lp_duality   Node: eeb507858cfa

Provenance: formalization of a published result. Source: EconCSLib, `linear_comb_lt_of_le_lt`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Simplex.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Convex combination of "≤ c" and "< c" stays "< c" (provided `α ≥ 0` and `α < 1`).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] in
set_option linter.unusedSectionVars false in
/-- Convex combination of "≤ c" and "< c" stays "< c" (provided `α ≥ 0` and `α < 1`). -/
theorem linear_comb_lt_of_le_lt (x y c : 𝕜) (H1 : x ≤ c) (H2 : y < c)
    {α : 𝕜} (hα₀ : 0 ≤ α) (hα₁ : α < 1) :
    α * x + (1 - α) * y < c := by
  have hpos : 0 < 1 - α := by linarith
  have hxc : 0 ≤ α * (c - x) := mul_nonneg hα₀ (by linarith)
  have hyc : 0 < (1 - α) * (c - y) := mul_pos hpos (by linarith)
  nlinarith
