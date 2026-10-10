import AFTD.Prelude
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexing
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingOnId
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingInvPerserveColor
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingToEquivSymmPerserveColor

/-!
# TensorSpecies.Tensor.IsReindexing.append_assoc_right

Topic: special_relativity   Node: da3daaacf242

Provenance: formalization of a published result. Source: Physlib, `TensorSpecies.Tensor.IsReindexing.append_assoc_right`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Reindexing.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

TensorSpecies.Tensor.IsReindexing.append_assoc_right
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TensorSpecies TensorSpecies.Tensor in
open Module in
variable {C : Type} in
open Fin in
lemma TensorSpecies.Tensor.IsReindexing.append_assoc_right   {n1 n2 n3 : ℕ} {c : Fin n1 → C} {c2 : Fin n2 → C} {c3 : Fin n3 → C} :
    IsReindexing (Fin.append c (Fin.append c2 c3)) (Fin.append (Fin.append c c2) c3)
      (Fin.cast (by grind)) :=
  ⟨(finCongr (by grind)).bijective, fun i => (congrFun (Fin.append_assoc c c2 c3) i).symm⟩
