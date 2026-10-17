import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixTraceLeft
import AFTD.Kb.Tcs.MatrixIsHermitianTraceLeft

/-!
# Matrix.PosSemidef.traceLeft

Topic: quantum   Node: 8b57359510a4

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.PosSemidef.traceLeft`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Matrix.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Matrix.PosSemidef.traceLeft
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open BigOperators in
variable {n 𝕜 : Type*} in
variable [RCLike 𝕜] [DecidableEq n] in
open scoped ComplexOrder MatrixOrder in
variable [AddCommMonoid R] [Fintype d] in
open ComplexOrder in
variable {d₁ d₂ : Type*} {A : Matrix (d₁ × d₂) (d₁ × d₂) 𝕜} in
variable [Fintype d₂] [Fintype d₁] in
theorem Matrix.PosSemidef.traceLeft [DecidableEq d₁] (hA : A.PosSemidef) : A.traceLeft.PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec] at hA ⊢
  constructor
  · exact hA.1.traceLeft
  · intro x
    convert Finset.sum_nonneg (s := .univ)
      (fun (i : d₁) _ ↦ hA.2 (fun (j,k) ↦ if i = j then x k else 0))
    simp_rw [Matrix.traceLeft, dotProduct_mulVec]
    simpa [dotProduct, vecMul_eq_sum, ite_apply, Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul,
      apply_ite] using Finset.sum_comm_cycle
