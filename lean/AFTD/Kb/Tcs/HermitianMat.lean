import AFTD.Prelude

/-!
# HermitianMat

Topic: quantum   Node: d72d0820e325

Provenance: formalization of a published result. Source: QuantumInfo, `HermitianMat`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HermitianMat/Basic.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The type of Hermitian matrices, as a `Subtype`. Equivalent to a `Matrix n n α` bundled with the fact that `Matrix.IsHermitian`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The type of Hermitian matrices, as a `Subtype`. Equivalent to a `Matrix n n α` bundled with the fact that `Matrix.IsHermitian`. -/
def HermitianMat (n : Type*) (α : Type*) [AddGroup α] [StarAddMonoid α] :=
  (selfAdjoint (Matrix n n α) : Type (max u_1 u_2))
