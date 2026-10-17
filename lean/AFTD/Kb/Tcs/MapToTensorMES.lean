import AFTD.Prelude

/-!
# map_to_tensor_MES

Topic: quantum   Node: 5764d99e9591

Provenance: formalization of a published result. Source: QuantumInfo, `map_to_tensor_MES`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/Entropy/SSA.lean (Copyright (c) 2026 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The matrix representation of the map $v \mapsto v \otimes \sum_k |k\rangle|k\rangle$. The output index is `(d1 \times d2) \times d2`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {d d₁ d₂ d₃ m n : Type*} in
variable [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃] [Fintype m] [Fintype n] in
variable [DecidableEq d] [DecidableEq d₁] [DecidableEq d₂] [DecidableEq d₃] [DecidableEq m] [DecidableEq n] in
variable {dA dB dC dA₁ dA₂ : Type*} in
variable [Fintype dA] [Fintype dB] [Fintype dC] [Fintype dA₁] [Fintype dA₂] in
variable [DecidableEq dA] [DecidableEq dB] [DecidableEq dC] [DecidableEq dA₁] [DecidableEq dA₂] in
variable {𝕜 : Type*} [RCLike 𝕜] in
variable {α : ℝ} in
open scoped InnerProductSpace RealInnerProductSpace Kronecker Matrix in
variable (d₁ d₂) in
/-- The matrix representation of the map $v \mapsto v \otimes \sum_k |k\rangle|k\rangle$. The output index is `(d1 \times d2) \times d2`. -/
noncomputable def map_to_tensor_MES : Matrix ((d₁ × d₂) × d₂) d₁ ℂ :=
  Matrix.of fun ((i, j), k) l => if i = l ∧ j = k then 1 else 0
