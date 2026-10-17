import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixKronUnitary

/-!
# Matrix.unitary_kron

Topic: quantum   Node: 5e305efa4ab5

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.unitary_kron`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HermitianMat/Unitary.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Matrix.unitary_kron
-/

set_option quotPrecheck false
local notation "𝐔[" n "]" => Matrix.unitaryGroup n ℂ

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
variable {α : Type*} [NonUnitalNonAssocSemiring α] [StarRing α] in
variable {α β : Type*} [DecidableEq α] [Fintype α] [DecidableEq β] [Fintype β] in
open Kronecker in
def Matrix.unitary_kron (a : 𝐔[α]) (b : 𝐔[β]) : 𝐔[α × β] :=
  ⟨_, kron_unitary a b⟩
