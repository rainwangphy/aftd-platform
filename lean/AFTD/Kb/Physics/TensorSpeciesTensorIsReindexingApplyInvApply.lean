import AFTD.Prelude
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexing
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingInv
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingToEquiv
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingOnId

/-!
# TensorSpecies.Tensor.IsReindexing.apply_inv_apply

Topic: special_relativity   Node: bec5a1f23e84

Provenance: formalization of a published result. Source: Physlib, `TensorSpecies.Tensor.IsReindexing.apply_inv_apply`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Reindexing.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

TensorSpecies.Tensor.IsReindexing.apply_inv_apply
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TensorSpecies TensorSpecies.Tensor TensorSpecies.Tensor.IsReindexing in
open Module in
variable {C : Type} in
lemma TensorSpecies.Tensor.IsReindexing.apply_inv_apply {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    (σ : Fin m → Fin n) (h : IsReindexing c c1 σ) (x : Fin m) :
    h.inv σ (σ x) = x := by
  change h.toEquiv (h.toEquiv.symm x) = x
  simp
