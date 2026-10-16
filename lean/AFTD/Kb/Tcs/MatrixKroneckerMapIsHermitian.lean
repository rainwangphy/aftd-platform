import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixKroneckerMapConjTranspose

/-!
# Matrix.kroneckerMap_IsHermitian

Topic: quantum   Node: b44dba47634e

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.kroneckerMap_IsHermitian`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Matrix.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Matrix.kroneckerMap_IsHermitian
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
variable {A : Matrix m m R} {B : Matrix n n R} in
variable (hA : A.IsHermitian) (hB : B.IsHermitian) in
include hA hB in
omit [DecidableEq n] in
theorem Matrix.kroneckerMap_IsHermitian : (A ⊗ₖ B).IsHermitian := by
  exact (hA ▸ hB ▸ kroneckerMap_conjTranspose A B : _ = _)
