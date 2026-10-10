import AFTD.Prelude
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexing
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingOnId
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingInvPerserveColor
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingToEquivSymmPerserveColor

/-!
# TensorSpecies.Tensor.IsReindexing.append_congr_right

Topic: special_relativity   Node: 6b8038fe8ac6

Provenance: formalization of a published result. Source: Physlib, `TensorSpecies.Tensor.IsReindexing.append_congr_right`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Reindexing.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

TensorSpecies.Tensor.IsReindexing.append_congr_right
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TensorSpecies TensorSpecies.Tensor in
open Module in
variable {C : Type} in
open Fin in
lemma TensorSpecies.Tensor.IsReindexing.append_congr_right {n n' n2 : ℕ} {c : Fin n → C} {c' : Fin n' → C}
    {σ : Fin n' → Fin n} (c2 : Fin n2 → C) (h : IsReindexing c c' σ) :
    IsReindexing (Fin.append c2 c) (Fin.append c2 c')
      (Fin.append (Fin.castAdd n) (Fin.natAdd n2 ∘ σ)) := by
  refine ⟨?_, fun i => ?_⟩
  · have heq : (Fin.append (Fin.castAdd n) (Fin.natAdd n2 ∘ σ) : Fin (n2 + n') → Fin (n2 + n)) =
        ⇑(finSumFinEquiv.symm.trans
          (((Equiv.refl (Fin n2)).sumCongr (Equiv.ofBijective σ h.1)).trans finSumFinEquiv)) := by
      ext i
      refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;>
        simp [Fin.append_left, Fin.append_right]
    rw [heq]
    exact Equiv.bijective _
  · refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;>
      simp [Fin.append_left, Fin.append_right, h.2]
