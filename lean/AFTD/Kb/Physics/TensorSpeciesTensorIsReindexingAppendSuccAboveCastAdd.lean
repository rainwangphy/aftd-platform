import AFTD.Prelude
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexing
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingOnId
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingInvPerserveColor
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingToEquivSymmPerserveColor
import AFTD.Kb.Tcs.ResolutionRefutationPosNegExample
import AFTD.Kb.Physics.FinSuccSuccAboveLeqIffLeq

/-!
# TensorSpecies.Tensor.IsReindexing.append_succAbove_castAdd

Topic: special_relativity   Node: 3d86d05113e0

Provenance: formalization of a published result. Source: Physlib, `TensorSpecies.Tensor.IsReindexing.append_succAbove_castAdd`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Reindexing.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

TensorSpecies.Tensor.IsReindexing.append_succAbove_castAdd
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TensorSpecies TensorSpecies.Tensor in
open Module in
variable {C : Type} in
open Fin in
lemma TensorSpecies.Tensor.IsReindexing.append_succAbove_castAdd {n n1 : ℕ} {c : Fin (n + 1) → C} {c1 : Fin (n1 + 1) → C}
    (i : Fin (n + 1)) :
    IsReindexing (Fin.append c c1 ∘ (Fin.castAdd (n1 + 1) i).succAbove)
      (Fin.append (c ∘ i.succAbove) c1) (Fin.cast (by grind)) := by
  refine ⟨(finCongr (by grind)).bijective, fun y => ?_⟩
  simp only [Function.comp_apply]
  refine Fin.addCases (fun a => ?_) (fun a => ?_) y
  · have hidx : (Fin.castAdd (n1 + 1) i).succAbove (Fin.cast (by grind) (Fin.castAdd (n1 + 1) a))
        = Fin.castAdd (n1 + 1) (i.succAbove a) := by
      have hcond : ((Fin.cast (by grind) (Fin.castAdd (n1 + 1) a)).castSucc <
          Fin.castAdd (n1 + 1) i) ↔ (a.castSucc < i) := by
        simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_cast, Fin.val_castAdd]
      simp only [Fin.succAbove, hcond]
      split_ifs <;> ext <;> simp
    simp [hidx, Fin.append_left]
  · have hidx : (Fin.castAdd (n1 + 1) i).succAbove (Fin.cast (by grind) (Fin.natAdd n a))
        = Fin.natAdd (n + 1) a := by
      rw [Fin.succAbove_of_le_castSucc]
      · ext
        simp [Nat.add_right_comm]
      · simp only [Fin.le_def, Fin.val_castSucc, Fin.val_cast, Fin.val_natAdd, Fin.val_castAdd]
        omega
    simp [hidx, Fin.append_right]
