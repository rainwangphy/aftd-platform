import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixIsometry
import AFTD.Kb.Tcs.MatrixTraceNorm
import AFTD.Kb.Tcs.MatrixTraceNormZero
import AFTD.Kb.Tcs.MatrixTraceNormNeg

/-!
# Matrix.traceNorm_isometry_right

Topic: quantum   Node: bd129a0b9ec0

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.traceNorm_isometry_right`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/MatrixNorm/TraceNorm.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The trace norm is invariant under right multiplication by the adjoint of an isometry.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open BigOperators in
open Classical in
open scoped ComplexOrder in
variable {m n R : Type*} in
variable [Fintype m] [Fintype n] in
variable [RCLike R] in
open MatrixOrder Isometry in
/-- The trace norm is invariant under right multiplication by the adjoint of an isometry. -/
theorem Matrix.traceNorm_isometry_right [Fintype k] {A : Matrix n m R} {u : Matrix k m R}
  (hu₁ : u.Isometry) : traceNorm (A * uᴴ) = traceNorm A := by
  unfold traceNorm
  congr 1
  simp [← Matrix.mul_assoc]
  nth_rw 2 [Matrix.mul_assoc]
  have hA := (Matrix.posSemidef_conjTranspose_mul_self A).nonneg
  have hsqrt : CFC.sqrt (u * (Aᴴ * A) * uᴴ) = u * CFC.sqrt (Aᴴ * A) * uᴴ := by
    have h_conj (B : Matrix m m R) (hB : 0 ≤ B) : 0 ≤ u * B * uᴴ := by
      rw [Matrix.nonneg_iff_posSemidef] at hB ⊢
      exact hB.mul_mul_conjTranspose_same u
    apply (CFC.sqrt_eq_iff _ _ (h_conj _ hA) (h_conj _ (CFC.sqrt_nonneg _))).mpr
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc uᴴ, ← Matrix.mul_assoc uᴴ]
    simp [show uᴴ * u = 1 from hu₁]
    rw [← Matrix.mul_assoc, Matrix.mul_assoc u, CFC.sqrt_mul_sqrt_self _ hA]
  rw [hsqrt, Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  simp [show uᴴ * u = 1 by exact hu₁]
