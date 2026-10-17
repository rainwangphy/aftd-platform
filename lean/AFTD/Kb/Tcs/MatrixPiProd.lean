import AFTD.Prelude

/-!
# Matrix.piProd

Topic: quantum   Node: 624d5c01000d

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.piProd`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Matrix.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Matrix.piProd
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open BigOperators in
variable {n 𝕜 : Type*} in
variable [RCLike 𝕜] [DecidableEq n] in
open scoped ComplexOrder MatrixOrder in
variable {ι : Type*} {d : ι → Type*} [fι : Fintype ι] in
variable {R : Type*} in
noncomputable def Matrix.piProd [CommMonoid R] (A : ∀ i, Matrix (d i) (d i) R) : Matrix (∀ i, d i) (∀ i, d i) R :=
  Matrix.of (fun j k : (∀ i, d i) ↦ ∏ i, A i (j i) (k i))
