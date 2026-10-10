import AFTD.Prelude

/-!
# TensorSpecies.Tensor.IsReindexing

Topic: special_relativity   Node: dbb8818b219c

Provenance: formalization of a published result. Source: Physlib, `TensorSpecies.Tensor.IsReindexing`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Reindexing.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given two lists of indices `c : Fin n → C` and `c1 : Fin m → C` a map `σ : Fin m → Fin n` satisfies the condition `IsReindexing c c1 σ` if it is: - A bijection - Forms a commutative triangle with `c` and `c1`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module in
variable {C : Type} in
/-- Given two lists of indices `c : Fin n → C` and `c1 : Fin m → C` a map `σ : Fin m → Fin n` satisfies the condition `IsReindexing c c1 σ` if it is: - A bijection - Forms a commutative triangle with `c` and `c1`. -/
def TensorSpecies.Tensor.IsReindexing {n m : ℕ} (c : Fin n → C) (c1 : Fin m → C)
    (σ : Fin m → Fin n) : Prop :=
  Function.Bijective σ ∧ ∀ i, c (σ i) = c1 i
