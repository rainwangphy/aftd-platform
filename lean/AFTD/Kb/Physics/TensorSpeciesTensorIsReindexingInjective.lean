import AFTD.Prelude
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexing

/-!
# TensorSpecies.Tensor.IsReindexing.injective

Topic: special_relativity   Node: 2c0428df5665

Provenance: formalization of a published result. Source: Physlib, `TensorSpecies.Tensor.IsReindexing.injective`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Reindexing.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

TensorSpecies.Tensor.IsReindexing.injective
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TensorSpecies TensorSpecies.Tensor in
open Module in
variable {C : Type} in
lemma TensorSpecies.Tensor.IsReindexing.injective {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    {σ : Fin m → Fin n} (h : IsReindexing c c1 σ) : Function.Injective σ := h.1.1
