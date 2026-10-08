import AFTD.Prelude
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.Optimization.StdSimplexContinuousCoord
import AFTD.Kb.Optimization.WsumPureApply

/-!
# wsum_continuous

Topic: lp_duality   Node: 35912b0a9f80

Provenance: formalization of a published result. Source: EconCSLib, `wsum_continuous`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Simplex.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`wsum (·) f` is continuous on the standard simplex over ℝ.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] in
set_option linter.unusedSectionVars false in
variable {I : Type*} [Fintype I] in
/-- `wsum (·) f` is continuous on the standard simplex over ℝ. -/
theorem wsum_continuous (f : I → ℝ) :
    Continuous fun x : stdSimplex ℝ I => wsum x f :=
  continuous_finset_sum _ fun i _ =>
    (stdSimplex.continuous_coord i).mul continuous_const
