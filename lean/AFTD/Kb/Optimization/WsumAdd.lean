import AFTD.Prelude
import AFTD.Kb.Optimization.Wsum

/-!
# wsum_add

Topic: lp_duality   Node: 65ff7476fd80

Provenance: formalization of a published result. Source: EconCSLib, `wsum_add`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Simplex.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Weighted sum is linear over addition.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] in
set_option linter.unusedSectionVars false in
/-- Weighted sum is linear over addition. -/
theorem wsum_add (x : stdSimplex 𝕜 I) (f g : I → 𝕜) :
    wsum x (f + g) = wsum x f + wsum x g := by
  simp [wsum, dotProduct, mul_add, Finset.sum_add_distrib]
