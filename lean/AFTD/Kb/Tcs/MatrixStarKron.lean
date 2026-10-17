import AFTD.Prelude

/-!
# Matrix.star_kron

Topic: quantum   Node: 8c2415e0f6e5

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.star_kron`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HermitianMat/Unitary.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Matrix.star_kron
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
variable {α : Type*} [NonUnitalNonAssocSemiring α] [StarRing α] in
variable {α β : Type*} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β] in
omit [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β] in
open Kronecker in
@[simp]
theorem Matrix.star_kron (a : Matrix α α ℂ) (b : Matrix β β ℂ) : star (a ⊗ₖ b) = (star a) ⊗ₖ (star b) := by
  ext _ _
  simp
