import AFTD.Prelude
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.Optimization.WsumLeWsum

/-!
# wsum_ge_wsum

Topic: lp_duality   Node: 9f8307245bad

Provenance: formalization of a published result. Source: EconCSLib, `wsum_ge_wsum`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Simplex.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Weighted sum respects `≥`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] in
set_option linter.unusedSectionVars false in
/-- Weighted sum respects `≥`. -/
theorem wsum_ge_wsum (x : stdSimplex 𝕜 I) {f g : I → 𝕜}
    (h : ∀ i, f i ≥ g i) : wsum x f ≥ wsum x g :=
  wsum_le_wsum x h
