import AFTD.Prelude
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexing
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingOnId
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingInvPerserveColor
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingToEquivSymmPerserveColor

/-!
# TensorSpecies.Tensor.IsReindexing.append_succ_last

Topic: special_relativity   Node: 8d46d55cb800

Provenance: formalization of a published result. Source: Physlib, `TensorSpecies.Tensor.IsReindexing.append_succ_last`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Reindexing.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Splitting a list of colours `c : Fin (n + 1) → C` into its first `n` entries and its last entry recovers `c`: the identity permutation matches `Fin.append (c ∘ (Fin.last n).succAbove) ![c (Fin.last n)]` with `c`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TensorSpecies TensorSpecies.Tensor TensorSpecies.Tensor.IsReindexing in
open Module in
variable {C : Type} in
open Fin in
/-- Splitting a list of colours `c : Fin (n + 1) → C` into its first `n` entries and its last entry recovers `c`: the identity permutation matches `Fin.append (c ∘ (Fin.last n).succAbove) ![c (Fin.last n)]` with `c`. -/
lemma TensorSpecies.Tensor.IsReindexing.append_succ_last {n : ℕ} (c : Fin (n + 1) → C) :
    IsReindexing (Fin.append (c ∘ (Fin.last n).succAbove) ![c (Fin.last n)]) c id := by
  rw [Fin.succAbove_last, on_id]
  refine Fin.addCases (fun i => ?_) (fun i => ?_)
  · simp only [Fin.append_left, Function.comp_apply]; rfl
  · fin_cases i; simp only [Fin.append_right, Matrix.cons_val_fin_one]; rfl
