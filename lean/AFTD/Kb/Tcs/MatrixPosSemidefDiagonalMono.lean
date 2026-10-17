import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixPosSemidefDiagonalMonotone

/-!
# Matrix.PosSemidef.diagonal_mono

Topic: quantum   Node: 037d966bb8bc

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.PosSemidef.diagonal_mono`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Matrix.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Matrix.PosSemidef.diagonal_mono
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix Matrix.PosSemidef in
open BigOperators in
variable {n 𝕜 : Type*} in
variable [RCLike 𝕜] [DecidableEq n] in
open scoped ComplexOrder MatrixOrder in
open scoped ComplexOrder in
open scoped MatrixOrder in
variable {n m 𝕜 : Type*} in
variable [Fintype n] [Fintype m] [RCLike 𝕜] [DecidableEq m] in
variable {A : Matrix n n 𝕜} {B : Matrix n n 𝕜} in
variable (hA : A.IsHermitian) (hB : B.IsHermitian) in
variable [DecidableEq n] in
omit [Fintype n] in
theorem Matrix.PosSemidef.diagonal_mono {d₁ d₂ : n → 𝕜} : d₁ ≤ d₂ → diagonal d₁ ≤ diagonal d₂ := diagonal_monotone.imp
