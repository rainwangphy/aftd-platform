import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixStarKron

/-!
# Matrix.kron_unitary

Topic: quantum   Node: 8ac19d79793c

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.kron_unitary`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HermitianMat/Unitary.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Matrix.kron_unitary
-/

set_option quotPrecheck false
local notation "𝐔[" n "]" => Matrix.unitaryGroup n ℂ

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
variable {α : Type*} [NonUnitalNonAssocSemiring α] [StarRing α] in
variable {α β : Type*} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β] in
open Kronecker in
theorem Matrix.kron_unitary (a : 𝐔[α]) (b : 𝐔[β]) : a.val ⊗ₖ b.val ∈ 𝐔[α × β] := by
  simp [Matrix.mem_unitaryGroup_iff, ← Matrix.mul_kronecker_mul]
