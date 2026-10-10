import AFTD.Prelude
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexing
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingInv
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingInvApplyApply
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingOnId

/-!
# TensorSpecies.Tensor.IsReindexing.inv_eq_self_of_pointwise_eq

Topic: special_relativity   Node: 55ca1127dcdf

Provenance: formalization of a published result. Source: Physlib, `TensorSpecies.Tensor.IsReindexing.inv_eq_self_of_pointwise_eq`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Reindexing.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

TensorSpecies.Tensor.IsReindexing.inv_eq_self_of_pointwise_eq
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TensorSpecies TensorSpecies.Tensor TensorSpecies.Tensor.IsReindexing in
open Module in
variable {C : Type} in
lemma TensorSpecies.Tensor.IsReindexing.inv_eq_self_of_pointwise_eq {n : ℕ} {c c1 : Fin n → C} {σ : Fin n → Fin n}
    (h : IsReindexing c c1 σ) (hσ : ∀ x, σ x = x) (x : Fin n) :
    h.inv σ x = x := by
  have hx := h.inv_apply_apply σ x
  rw [hσ] at hx
  exact hx
