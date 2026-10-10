import AFTD.Prelude
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexing
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingOnId
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingInvPerserveColor
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingToEquivSymmPerserveColor

/-!
# TensorSpecies.Tensor.IsReindexing.update_update_of_eq

Topic: special_relativity   Node: 0434d3e512a3

Provenance: formalization of a published result. Source: Physlib, `TensorSpecies.Tensor.IsReindexing.update_update_of_eq`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Reindexing.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Updating slot `i` of `c` to `d` and then back to `e = c i` returns `c`, no other slot moving: the colour cast a round trip of two contractions at slot `i` generates.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TensorSpecies TensorSpecies.Tensor TensorSpecies.Tensor.IsReindexing in
open Module in
variable {C : Type} in
open Fin in
/-- Updating slot `i` of `c` to `d` and then back to `e = c i` returns `c`, no other slot moving: the colour cast a round trip of two contractions at slot `i` generates. -/
lemma TensorSpecies.Tensor.IsReindexing.update_update_of_eq {n : ℕ} {c : Fin n → C} {d e : C} (i : Fin n) (he : c i = e) :
    IsReindexing c (Function.update (Function.update c i d) i e) (id : Fin n → Fin n) :=
  on_id.mpr (fun j => by by_cases h : j = i <;> simp [h, Function.update_of_ne, he])
