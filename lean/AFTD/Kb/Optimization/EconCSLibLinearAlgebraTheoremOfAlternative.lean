import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraIsFeasible
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraHasCertificate
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraTheoremOfAlternativeAux
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraRowEvalDef

/-!
# EconCSLib.LinearAlgebra.theorem_of_alternative

Topic: lp_duality   Node: bd83ff27e8e9

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearAlgebra.theorem_of_alternative`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearAlgebra/FourierMotzkin.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Theorem of the Alternative** [MFoGT, Section 2.8, Exercise 7]: for a finite system of weak linear inequalities `A x ≥ b` over a linearly ordered field, exactly one of the primal `S = {x | Ax ≥ b}` and the Farkas certificate set `T = {u ≥ 0 | uᵀA = 0, ⟨u, b⟩ > 0}` is nonempty. Combines `feas_cert_disjoint` (disjointness) with the existence direction proved by Fourier-Motzkin elimination + induction on the number of variables (`theorem_of_alternative_aux`).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
/-- **Theorem of the Alternative** [MFoGT, Section 2.8, Exercise 7]: for a finite system of weak linear inequalities `A x ≥ b` over a linearly ordered field, exactly one of the primal `S = {x | Ax ≥ b}` and the Farkas certificate set `T = {u ≥ 0 | uᵀA = 0, ⟨u, b⟩ > 0}` is nonempty. Combines `feas_cert_disjoint` (disjointness) with the existence direction proved by Fourier-Motzkin elimination + induction on the number of variables (`theorem_of_alternative_aux`). -/
theorem EconCSLib.LinearAlgebra.theorem_of_alternative {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ}
    (A : I → Fin n → 𝕜) (b : I → 𝕜) :
    ¬ IsFeasible A b ↔ HasCertificate A b :=
  theorem_of_alternative_aux n A b
