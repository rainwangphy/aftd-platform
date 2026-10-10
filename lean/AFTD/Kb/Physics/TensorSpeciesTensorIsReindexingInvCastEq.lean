import AFTD.Prelude
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexing
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingInv
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingInvApplyApply
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingOnId
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingSymm

/-!
# TensorSpecies.Tensor.IsReindexing.inv_cast_eq

Topic: special_relativity   Node: 95504cdd6a54

Provenance: formalization of a published result. Source: Physlib, `TensorSpecies.Tensor.IsReindexing.inv_cast_eq`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Reindexing.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

TensorSpecies.Tensor.IsReindexing.inv_cast_eq
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TensorSpecies TensorSpecies.Tensor TensorSpecies.Tensor.IsReindexing in
open Module in
variable {C : Type} in
lemma TensorSpecies.Tensor.IsReindexing.inv_cast_eq {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C} (e : m = n)
    (h : IsReindexing c c1 (Fin.cast e)) (x : Fin n) :
    h.inv (Fin.cast e) x = Fin.cast e.symm x := by
  have hx := h.inv_apply_apply (Fin.cast e) x
  have hval : (h.inv (Fin.cast e) x).val = x.val := congrArg Fin.val hx
  exact Fin.val_inj.mp hval
