import AFTD.Prelude

/-!
# Matrix.kroneckerMap_conjTranspose

Topic: quantum   Node: 01c423b5995b

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.kroneckerMap_conjTranspose`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Matrix.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Matrix.kroneckerMap_conjTranspose
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open BigOperators in
variable {n 𝕜 : Type*} in
variable [RCLike 𝕜] [DecidableEq n] in
open scoped ComplexOrder MatrixOrder in
open Kronecker in
variable [CommRing R] [StarRing R] in
variable (A : Matrix m m R) (B : Matrix n n R) in
omit [DecidableEq n] in
theorem Matrix.kroneckerMap_conjTranspose : (A ⊗ₖ B)ᴴ = (Aᴴ ⊗ₖ Bᴴ) := by
  ext; simp
