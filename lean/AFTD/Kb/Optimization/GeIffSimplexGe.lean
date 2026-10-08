import AFTD.Prelude
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.Optimization.WsumConst
import AFTD.Kb.Optimization.WsumLeWsum
import AFTD.Kb.Optimization.StdSimplexPure
import AFTD.Kb.Optimization.WsumPureApply
import AFTD.Kb.Optimization.StdSimplexPureApply

/-!
# ge_iff_simplex_ge

Topic: lp_duality   Node: f9fc74069215

Provenance: formalization of a published result. Source: EconCSLib, `ge_iff_simplex_ge`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Simplex.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`f ≥ v` pointwise iff every simplex weighted sum is `≥ v`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] in
set_option linter.unusedSectionVars false in
/-- `f ≥ v` pointwise iff every simplex weighted sum is `≥ v`. -/
theorem ge_iff_simplex_ge {f : I → 𝕜} {v : 𝕜} :
    (∀ i, v ≤ f i) ↔ ∀ x : stdSimplex 𝕜 I, v ≤ wsum x f := by
  classical
  refine ⟨fun hi x => ?_, fun H i => ?_⟩
  · calc v = wsum x (fun _ => v) := (wsum_const x v).symm
      _ ≤ wsum x f := wsum_le_wsum x hi
  · simpa using H (stdSimplex.pure i)
