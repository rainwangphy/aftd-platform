import AFTD.Prelude

/-!
# RCLike.normSq_eq_conj_mul_self

Topic: quantum   Node: 2fcfed41137b

Provenance: formalization of a published result. Source: QuantumInfo, `RCLike.normSq_eq_conj_mul_self`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Matrix.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

RCLike.normSq_eq_conj_mul_self
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
open ComplexConjugate in
theorem RCLike.normSq_eq_conj_mul_self {z : 𝕜} : RCLike.normSq z = conj z * z := by
  rw [RCLike.ext_iff]
  simp [RCLike.normSq]
  ring_nf

--PR
