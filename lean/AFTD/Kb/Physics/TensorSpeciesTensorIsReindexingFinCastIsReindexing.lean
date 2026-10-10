import AFTD.Prelude
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexing
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingOnId
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingInvPerserveColor
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingToEquivSymmPerserveColor

/-!
# TensorSpecies.Tensor.IsReindexing.fin_cast_isReindexing

Topic: special_relativity   Node: 0db68d621ee4

Provenance: formalization of a published result. Source: Physlib, `TensorSpecies.Tensor.IsReindexing.fin_cast_isReindexing`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Reindexing.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Casting the domain along an equality `n1 = n` of lengths is a reindexing of `c` by `c ∘ Fin.cast h`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TensorSpecies TensorSpecies.Tensor in
open Module in
variable {C : Type} in
open Fin in
/-- Casting the domain along an equality `n1 = n` of lengths is a reindexing of `c` by `c ∘ Fin.cast h`. -/
lemma TensorSpecies.Tensor.IsReindexing.fin_cast_isReindexing (n n1 : ℕ) {c : Fin n → C} (h : n1 = n) :
    IsReindexing c (c ∘ Fin.cast h) (Fin.cast h) := by
  apply And.intro
  · exact Equiv.bijective (finCongr h)
  · intro i
    rfl
