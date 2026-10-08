import AFTD.Prelude
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.Optimization.StdSimplexPure
import AFTD.Kb.Optimization.StdSimplexPureApply

/-!
# wsum_pure_apply

Topic: lp_duality   Node: 838a59e8ef9d

Provenance: formalization of a published result. Source: EconCSLib, `wsum_pure_apply`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Simplex.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Weighted sum at a point mass evaluates the chosen coordinate.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] in
set_option linter.unusedSectionVars false in
/-- Weighted sum at a point mass evaluates the chosen coordinate. -/
@[simp]
theorem wsum_pure_apply [DecidableEq I] (i₀ : I) (f : I → 𝕜) :
    wsum (stdSimplex.pure (𝕜 := 𝕜) i₀) f = f i₀ := by
  change (∑ i, (if i = i₀ then (1 : 𝕜) else 0) * f i) = f i₀
  simp
