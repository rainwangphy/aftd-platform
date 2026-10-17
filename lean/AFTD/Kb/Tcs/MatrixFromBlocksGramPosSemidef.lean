import AFTD.Prelude

/-!
# Matrix.fromBlocks_gram_posSemidef

Topic: quantum   Node: cd783951f504

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.fromBlocks_gram_posSemidef`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Matrix.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The block Gram matrix `[[YᴴY, YᴴX], [XᴴY, XᴴX]]` is positive semidefinite.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open BigOperators in
variable {n 𝕜 : Type*} in
variable [RCLike 𝕜] [DecidableEq n] in
open scoped ComplexOrder MatrixOrder in
omit [DecidableEq n] in
/-- The block Gram matrix `[[YᴴY, YᴴX], [XᴴY, XᴴX]]` is positive semidefinite. -/
theorem Matrix.fromBlocks_gram_posSemidef {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]
    (X : Matrix k n ℂ) (Y : Matrix k m ℂ) :
    (fromBlocks (Yᴴ * Y) (Yᴴ * X) (Xᴴ * Y) (Xᴴ * X)).PosSemidef := by
  convert posSemidef_conjTranspose_mul_self
    (fromBlocks Y X (0 : Matrix k m ℂ) (0 : Matrix k n ℂ)) using 1
  rw [fromBlocks_conjTranspose, fromBlocks_multiply]
  simp
