import AFTD.Prelude
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexing

/-!
# TensorSpecies.Tensor.IsReindexing.on_id

Topic: special_relativity   Node: 493f27031953

Provenance: formalization of a published result. Source: Physlib, `TensorSpecies.Tensor.IsReindexing.on_id`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Reindexing.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

TensorSpecies.Tensor.IsReindexing.on_id
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TensorSpecies TensorSpecies.Tensor in
open Module in
variable {C : Type} in
@[simp]
lemma TensorSpecies.Tensor.IsReindexing.on_id {n : ℕ} {c c1 : Fin n → C} :
    IsReindexing c c1 (id : Fin n → Fin n) ↔ ∀ i, c i = c1 i := by
  simp [IsReindexing]
