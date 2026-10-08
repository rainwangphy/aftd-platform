import AFTD.Prelude

/-!
# wsum

Topic: lp_duality   Node: 4770d96c14ca

Provenance: formalization of a published result. Source: EconCSLib, `wsum`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Simplex.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Weighted sum of `f` with weights from a simplex element `x`. Thin `abbrev` over Mathlib's finite dot product `⬝ᵥ`: definitionally equal, so `simp [wsum]` (or no unfold at all) switches between the two forms. Kept as a named concept because the simplex-specific lemmas below (`wsum_const`, `wsum_le_wsum`, `wsum_nonneg`, `wsum_pure`) depend on `∑ x = 1` or `x ≥ 0` and have no generic `dotProduct` analogue.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] in
set_option linter.unusedSectionVars false in
/-- Weighted sum of `f` with weights from a simplex element `x`. Thin `abbrev` over Mathlib's finite dot product `⬝ᵥ`: definitionally equal, so `simp [wsum]` (or no unfold at all) switches between the two forms. Kept as a named concept because the simplex-specific lemmas below (`wsum_const`, `wsum_le_wsum`, `wsum_nonneg`, `wsum_pure`) depend on `∑ x = 1` or `x ≥ 0` and have no generic `dotProduct` analogue. -/
abbrev wsum (x : stdSimplex 𝕜 I) (f : I → 𝕜) : 𝕜 :=
  x ⬝ᵥ f
