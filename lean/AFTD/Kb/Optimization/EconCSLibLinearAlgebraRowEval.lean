import AFTD.Prelude

/-!
# EconCSLib.LinearAlgebra.rowEval

Topic: lp_duality   Node: a0e12b9600ce

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearAlgebra.rowEval`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearAlgebra/FourierMotzkin.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Evaluate the LHS of row `i` of the matrix `A : I → Fin n → 𝕜` at the point `x : Fin n → 𝕜`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Evaluate the LHS of row `i` of the matrix `A : I → Fin n → 𝕜` at the point `x : Fin n → 𝕜`. -/
def EconCSLib.LinearAlgebra.rowEval {I : Type*} {n : ℕ} [Fintype I] (A : I → Fin n → 𝕜) (i : I)
    (x : Fin n → 𝕜) : 𝕜 :=
  ∑ j, A i j * x j
