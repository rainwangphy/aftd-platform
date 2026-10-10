import AFTD.Prelude
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexing
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingInv
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingInvApplyApply
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingOnId
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingInjective
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingSymm

/-!
# TensorSpecies.Tensor.IsReindexing.inv_equiv_symm_eq

Topic: special_relativity   Node: 48b6f8af7f9e

Provenance: formalization of a published result. Source: Physlib, `TensorSpecies.Tensor.IsReindexing.inv_equiv_symm_eq`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Reindexing.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

TensorSpecies.Tensor.IsReindexing.inv_equiv_symm_eq
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TensorSpecies TensorSpecies.Tensor TensorSpecies.Tensor.IsReindexing in
open Module in
variable {C : Type} in
lemma TensorSpecies.Tensor.IsReindexing.inv_equiv_symm_eq {n : ℕ} {c c1 : Fin n → C} (e : Equiv.Perm (Fin n))
    (h : IsReindexing c c1 ⇑e.symm) (x : Fin n) :
    h.inv ⇑e.symm x = e x := by
  have hx := h.inv_apply_apply ⇑e.symm x
  apply e.symm.injective
  rw [hx, Equiv.symm_apply_apply]
