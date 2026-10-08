import AFTD.Prelude
import AFTD.Kb.Optimization.ExpectedPayoffMatrix
import AFTD.Kb.Optimization.WsumWsumComm
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.Optimization.WsumPureApply

/-!
# expectedPayoffMatrix_comm

Topic: lp_duality   Node: 28171d3c5eb5

Provenance: formalization of a published result. Source: EconCSLib, `expectedPayoffMatrix_comm`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Simplex.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Expected payoff is commutative in the summation order.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] in
set_option linter.unusedSectionVars false in
variable {J : Type*} in
open Matrix in
/-- Expected payoff is commutative in the summation order. -/
theorem expectedPayoffMatrix_comm {J : Type*} [Fintype J]
    (A : I → J → 𝕜) (x : stdSimplex 𝕜 I) (y : stdSimplex 𝕜 J) :
    expectedPayoffMatrix A x y =
    y ⬝ᵥ fun j => x ⬝ᵥ fun i => A i j := by
  simpa [expectedPayoffMatrix, wsum] using wsum_wsum_comm x y A
