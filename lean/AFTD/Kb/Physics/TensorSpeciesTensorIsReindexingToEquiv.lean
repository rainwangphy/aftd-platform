import AFTD.Prelude
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexing
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingInv
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingOnId

/-!
# TensorSpecies.Tensor.IsReindexing.toEquiv

Topic: special_relativity   Node: 898addeca4c4

Provenance: formalization of a published result. Source: Physlib, `TensorSpecies.Tensor.IsReindexing.toEquiv`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Reindexing.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For a map `σ : Fin m → Fin n` satisfying `IsReindexing c c1 σ`, that map lifted to an equivalence between `Fin n` and `Fin m`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TensorSpecies TensorSpecies.Tensor TensorSpecies.Tensor.IsReindexing in
open Module in
variable {C : Type} in
/-- For a map `σ : Fin m → Fin n` satisfying `IsReindexing c c1 σ`, that map lifted to an equivalence between `Fin n` and `Fin m`. -/
def TensorSpecies.Tensor.IsReindexing.toEquiv {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    {σ : Fin m → Fin n} (h : IsReindexing c c1 σ) :
    Fin n ≃ Fin m where
  toFun := inv σ h
  invFun := σ
  left_inv := Fintype.rightInverse_bijInv h.1
  right_inv := Fintype.leftInverse_bijInv h.1
