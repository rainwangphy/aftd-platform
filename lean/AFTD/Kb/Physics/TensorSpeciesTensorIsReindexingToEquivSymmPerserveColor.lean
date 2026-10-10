import AFTD.Prelude
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexing
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingToEquiv
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingPreserveColor
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingOnId
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingInvPerserveColor

/-!
# TensorSpecies.Tensor.IsReindexing.toEquiv_symm_perserve_color

Topic: special_relativity   Node: d96252454e9b

Provenance: formalization of a published result. Source: Physlib, `TensorSpecies.Tensor.IsReindexing.toEquiv_symm_perserve_color`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Reindexing.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

TensorSpecies.Tensor.IsReindexing.toEquiv_symm_perserve_color
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TensorSpecies TensorSpecies.Tensor TensorSpecies.Tensor.IsReindexing in
open Module in
variable {C : Type} in
set_option warning.simp.varHead false in
@[simp]
lemma TensorSpecies.Tensor.IsReindexing.toEquiv_symm_perserve_color {n m : ℕ} {c : Fin n → C} {c1 : Fin m → C}
    {σ : Fin m → Fin n} (h : IsReindexing c c1 σ) (x : Fin m) :
    c (h.toEquiv.symm x) = c1 x := by
  obtain ⟨x, rfl⟩ := h.toEquiv.surjective x
  rw [h.preserve_color]
  rfl
