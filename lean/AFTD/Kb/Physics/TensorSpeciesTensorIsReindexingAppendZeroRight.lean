import AFTD.Prelude
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexing
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingOnId
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingInvPerserveColor
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingToEquivSymmPerserveColor

/-!
# TensorSpecies.Tensor.IsReindexing.append_zero_right

Topic: special_relativity   Node: 5913c54ac4d0

Provenance: formalization of a published result. Source: Physlib, `TensorSpecies.Tensor.IsReindexing.append_zero_right`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Reindexing.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

TensorSpecies.Tensor.IsReindexing.append_zero_right
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TensorSpecies TensorSpecies.Tensor TensorSpecies.Tensor.IsReindexing in
open Module in
variable {C : Type} in
open Fin in
lemma TensorSpecies.Tensor.IsReindexing.append_zero_right {n} {c : Fin n → C}
    {c1 : Fin 0 → C} : IsReindexing c (Fin.append c c1) id := by
  simp only [Nat.add_zero, IsReindexing.on_id]
  have P : ∀ (i : Fin (n + 0)), c i = Fin.append c c1 i := by
    rw [Fin.forall_fin_add]
    simp only [Fin.append_left, Fin.append_right, IsEmpty.forall_iff, and_true]
    simp only [Fin.castAdd_zero, Fin.cast_eq_self, implies_true]
  exact P
