import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraRowEval

/-!
# EconCSLib.LinearAlgebra.IsFeasible

Topic: lp_duality   Node: 6ce31ef57757

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearAlgebra.IsFeasible`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearAlgebra/FourierMotzkin.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Primal feasibility of the system `A x ≥ b`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Primal feasibility of the system `A x ≥ b`. -/
def EconCSLib.LinearAlgebra.IsFeasible {I : Type*} {n : ℕ} [Fintype I] (A : I → Fin n → 𝕜)
    (b : I → 𝕜) : Prop :=
  ∃ x : Fin n → 𝕜, ∀ i, b i ≤ rowEval A i x
