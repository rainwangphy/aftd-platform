import AFTD.Prelude
import AFTD.Kb.Optimization.Wsum

/-!
# wsum_wsum_comm

Topic: lp_duality   Node: 9d03501fd76a

Provenance: formalization of a published result. Source: EconCSLib, `wsum_wsum_comm`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Simplex.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Exchange order of double weighted sums.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] in
set_option linter.unusedSectionVars false in
/-- Exchange order of double weighted sums. -/
theorem wsum_wsum_comm {J : Type*} [Fintype J]
    (x : stdSimplex 𝕜 I) (y : stdSimplex 𝕜 J)
    (A : I → J → 𝕜) :
    wsum x (fun i => wsum y (A i)) = wsum y (fun j => wsum x (fun i => A i j)) := by
  simp only [wsum, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  ext j
  congr 1
  ext i
  ring
