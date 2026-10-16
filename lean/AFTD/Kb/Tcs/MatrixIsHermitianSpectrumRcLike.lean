import AFTD.Prelude

/-!
# Matrix.IsHermitian.spectrum_rcLike

Topic: quantum   Node: e9d16ab7f28c

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.IsHermitian.spectrum_rcLike`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HermitianMat/Basic.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Matrix.IsHermitian.spectrum_rcLike
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {α R 𝕜 : Type*} {m n : Type*} in
variable [Star R] [TrivialStar R] in
variable [RCLike 𝕜] in
variable {d d₂ : Type*} [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂] in
variable [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] in
theorem Matrix.IsHermitian.spectrum_rcLike {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    RCLike.ofReal '' spectrum ℝ A = spectrum 𝕜 A := by
  rw [hA.spectrum_eq_image_range, hA.spectrum_real_eq_range_eigenvalues]
