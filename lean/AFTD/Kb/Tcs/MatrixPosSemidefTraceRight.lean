import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixTraceRight
import AFTD.Kb.Tcs.MatrixIsHermitianTraceRight

/-!
# Matrix.PosSemidef.traceRight

Topic: quantum   Node: be3af3c6d27d

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.PosSemidef.traceRight`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Matrix.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Matrix.PosSemidef.traceRight
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
theorem Matrix.PosSemidef.traceRight [DecidableEq d₂] (hA : A.PosSemidef) : A.traceRight.PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec] at hA ⊢
  constructor
  · exact hA.1.traceRight
  · intro x
    convert Finset.sum_nonneg (s := .univ)
      (fun (i : d₂) _ ↦ hA.2 (fun (j,k) ↦ if i = k then x j else 0))
    simp_rw [Matrix.traceRight, dotProduct_mulVec]
    simpa [dotProduct, vecMul_eq_sum, ite_apply, Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul,
      apply_ite] using Finset.sum_comm_cycle
