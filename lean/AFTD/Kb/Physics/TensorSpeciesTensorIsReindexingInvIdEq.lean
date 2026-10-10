import AFTD.Prelude
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexing
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingInv
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingInvApplyApply
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingOnId

/-!
# TensorSpecies.Tensor.IsReindexing.inv_id_eq

Topic: special_relativity   Node: 010ec89ac547

Provenance: formalization of a published result. Source: Physlib, `TensorSpecies.Tensor.IsReindexing.inv_id_eq`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Reindexing.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

TensorSpecies.Tensor.IsReindexing.inv_id_eq
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TensorSpecies TensorSpecies.Tensor TensorSpecies.Tensor.IsReindexing in
open Module in
variable {C : Type} in
lemma TensorSpecies.Tensor.IsReindexing.inv_id_eq {n : ℕ} {c c1 : Fin n → C}
    (h : IsReindexing c c1 (id : Fin n → Fin n)) (x : Fin n) :
    h.inv (id : Fin n → Fin n) x = x :=
  h.inv_apply_apply (id : Fin n → Fin n) x
