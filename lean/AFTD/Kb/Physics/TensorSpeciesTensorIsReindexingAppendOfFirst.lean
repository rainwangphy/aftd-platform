import AFTD.Prelude
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexing
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingOnId
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingInvPerserveColor
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingToEquivSymmPerserveColor

/-!
# TensorSpecies.Tensor.IsReindexing.append_of_first

Topic: special_relativity   Node: a51f783e9a61

Provenance: formalization of a published result. Source: Physlib, `TensorSpecies.Tensor.IsReindexing.append_of_first`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Reindexing.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Splitting a list of colours `c : Fin (n + 1) → C` into its first entry and its remaining `n` entries recovers `c`: the canonical reindexing `Fin (1 + n) ≃ Fin (n + 1)` matches `Fin.append ![c 0] (c ∘ Fin.succAbove 0)` with `c`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TensorSpecies TensorSpecies.Tensor in
open Module in
variable {C : Type} in
open Fin in
/-- Splitting a list of colours `c : Fin (n + 1) → C` into its first entry and its remaining `n` entries recovers `c`: the canonical reindexing `Fin (1 + n) ≃ Fin (n + 1)` matches `Fin.append ![c 0] (c ∘ Fin.succAbove 0)` with `c`. -/
lemma TensorSpecies.Tensor.IsReindexing.append_of_first {n : ℕ} (c : Fin (n + 1) → C) :
    IsReindexing (Fin.append ![c 0] (c ∘ Fin.succAbove 0)) c (Fin.cast (by grind)) := by
  refine ⟨(finCongr (by grind)).bijective, fun i => ?_⟩
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i, rfl⟩
  · rfl
  · simpa using congrArg (Fin.append ![c 0] (c ∘ Fin.succ)) (a₁ := Fin.cast _ i.succ)
      (a₂ := Fin.natAdd 1 i) (by ext; grind)
