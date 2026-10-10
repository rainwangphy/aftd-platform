import AFTD.Prelude
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexing
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingOnId
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingInvPerserveColor
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingToEquivSymmPerserveColor
import AFTD.Kb.Tcs.ResolutionRefutationPosNegExample

/-!
# TensorSpecies.Tensor.IsReindexing.append_succAbove_natAdd

Topic: special_relativity   Node: e92c48d4a0a0

Provenance: formalization of a published result. Source: Physlib, `TensorSpecies.Tensor.IsReindexing.append_succAbove_natAdd`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Reindexing.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

TensorSpecies.Tensor.IsReindexing.append_succAbove_natAdd
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TensorSpecies TensorSpecies.Tensor in
open Module in
variable {C : Type} in
open Fin in
lemma TensorSpecies.Tensor.IsReindexing.append_succAbove_natAdd {n n1 : ℕ} {c : Fin n → C} {c1 : Fin (n1 + 1) → C}
    (i : Fin (n1 + 1)) :
    IsReindexing (Fin.append c c1 ∘ (Fin.natAdd n i).succAbove)
      (Fin.append c (c1 ∘ i.succAbove)) id := by
  refine ⟨Function.bijective_id, fun x => ?_⟩
  simp only [Function.comp_apply, id_eq]
  refine Fin.addCases (fun a => ?_) (fun a => ?_) x
  · have hidx : (Fin.natAdd n i).succAbove (Fin.castAdd n1 a) = Fin.castAdd (n1 + 1) a := by
      rw [Fin.succAbove_of_castSucc_lt]
      · ext
        simp
      · simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_castAdd, Fin.val_natAdd]
        omega
    simp [hidx, Fin.append_left]
  · have hidx : (Fin.natAdd n i).succAbove (Fin.natAdd n a) = Fin.natAdd n (i.succAbove a) := by
      have hcond : ((Fin.natAdd n a).castSucc < Fin.natAdd n i) ↔ (a.castSucc < i) := by
        simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_natAdd]
        omega
      simp only [Fin.succAbove, hcond]
      split_ifs <;> ext <;> simp [Nat.add_assoc]
    simp [hidx, Fin.append_right]
