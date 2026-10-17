import AFTD.Prelude
import AFTD.Kb.Tcs.RCLikeNormSqEqConjMulSelf

/-!
# Matrix.PosSemidef.outer_self_conj

Topic: quantum   Node: 00d4624e53eb

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.PosSemidef.outer_self_conj`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Matrix.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Matrix.PosSemidef.outer_self_conj
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix Matrix.PosSemidef in
open BigOperators in
variable {n 𝕜 : Type*} in
variable [RCLike 𝕜] [DecidableEq n] in
open scoped ComplexOrder MatrixOrder in
open Kronecker in
open scoped ComplexOrder in
variable {m n 𝕜 : Type*} in
variable [Fintype m] [Fintype n] in
variable [RCLike 𝕜] [dn : DecidableEq n] in
variable {A : Matrix m m 𝕜} {B : Matrix m m 𝕜} in
variable (hA : A.PosSemidef) (hB : B.PosSemidef) in
omit dn in
open ComplexConjugate in
theorem Matrix.PosSemidef.outer_self_conj (v : n → 𝕜) : PosSemidef (vecMulVec v (conj v)) := by
  constructor
  · ext
    simp [vecMulVec_apply, mul_comm]
  · intro x
    rw [Finsupp.sum_fintype _ _ (by simp)]
    conv =>
      enter [2, 2, i]
      rw [Finsupp.sum_fintype _ _ (by simp)]
    simp_rw [RCLike.star_def,
      vecMulVec_apply, mul_assoc, ← Finset.mul_sum, ← mul_assoc, ← Finset.sum_mul]
    change
      0 ≤ (∑ i : n, conj (x i) * v i) * ∑ i : n, conj (v i) * x i
    have : (∑ i : n, conj (x i) * v i) =
        (∑ i : n, conj (conj (v i) * x i)) := by
          simp only [mul_comm (conj (x _)) (v _), map_mul,
          RingHomCompTriple.comp_apply, RingHom.id_apply]
    rw [this, ← map_sum, ← RCLike.normSq_eq_conj_mul_self, RCLike.ofReal_nonneg]
    exact RCLike.normSq_nonneg _
