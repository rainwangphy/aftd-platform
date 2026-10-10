import AFTD.Prelude
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexing
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingOnId
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingInvPerserveColor
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingToEquivSymmPerserveColor

/-!
# TensorSpecies.Tensor.IsReindexing.succAbove_succAbove_comm

Topic: special_relativity   Node: d059279131d6

Provenance: formalization of a published result. Source: Physlib, `TensorSpecies.Tensor.IsReindexing.succAbove_succAbove_comm`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Reindexing.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Removing two single entries from `c` in either order gives the same colour list: removing the `k1`-th entry and then the (shifted) `k2`-th entry matches removing the `k2`-th entry first and then the (shifted) `k1`-th entry, via the identity permutation. This is used for the commutation of two *evaluations* of indices.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TensorSpecies TensorSpecies.Tensor in
open Module in
variable {C : Type} in
open Fin in
/-- Removing two single entries from `c` in either order gives the same colour list: removing the `k1`-th entry and then the (shifted) `k2`-th entry matches removing the `k2`-th entry first and then the (shifted) `k1`-th entry, via the identity permutation. This is used for the commutation of two *evaluations* of indices. -/
lemma TensorSpecies.Tensor.IsReindexing.succAbove_succAbove_comm {n : ℕ} {c : Fin (n + 1 + 1) → C}
    (k1 : Fin (n + 1 + 1)) (k2 : Fin (n + 1)) :
    let k2' := k1.succAbove k2;
    let k1' := k2.predAbove k1;
    IsReindexing ((c ∘ k2'.succAbove) ∘ k1'.succAbove)
      ((c ∘ k1.succAbove) ∘ k2.succAbove) id := by
  intro k2' k1'
  refine ⟨Function.bijective_id, fun m => ?_⟩
  simp only [id_eq, Function.comp_apply]
  congr 1
  exact Fin.succAbove_succAbove_succAbove_predAbove k1 k2 m
