import AFTD.Prelude

/-!
# stdSimplex.continuous_coord

Topic: lp_duality   Node: 636455490330

Provenance: formalization of a published result. Source: EconCSLib, `stdSimplex.continuous_coord`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Simplex.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The `i`-th coordinate projection on `stdSimplex ℝ I` is continuous.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] in
set_option linter.unusedSectionVars false in
variable {I : Type*} [Fintype I] in
/-- The `i`-th coordinate projection on `stdSimplex ℝ I` is continuous. -/
theorem stdSimplex.continuous_coord (i : I) :
    Continuous fun x : stdSimplex ℝ I => x.val i :=
  (continuous_apply i).comp continuous_subtype_val
