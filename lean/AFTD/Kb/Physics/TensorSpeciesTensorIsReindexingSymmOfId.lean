import AFTD.Prelude
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexing
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingOnId
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingInvPerserveColor
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingToEquivSymmPerserveColor
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingSymm

/-!
# TensorSpecies.Tensor.IsReindexing.symm_of_id

Topic: special_relativity   Node: d3b0d412ace9

Provenance: formalization of a published result. Source: Physlib, `TensorSpecies.Tensor.IsReindexing.symm_of_id`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Reindexing.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

TensorSpecies.Tensor.IsReindexing.symm_of_id
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TensorSpecies TensorSpecies.Tensor TensorSpecies.Tensor.IsReindexing in
open Module in
variable {C : Type} in
open Fin in
lemma TensorSpecies.Tensor.IsReindexing.symm_of_id {n : ℕ} {c c1 : Fin n → C} (h : IsReindexing c c1 id) :
    IsReindexing c1 c id := by
  simp at h ⊢
  exact fun i => (h i).symm
