import AFTD.Prelude
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexing
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingOnId
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingInvPerserveColor
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingToEquivSymmPerserveColor

/-!
# TensorSpecies.Tensor.IsReindexing.comp

Topic: special_relativity   Node: a5f6f75aa91f

Provenance: formalization of a published result. Source: Physlib, `TensorSpecies.Tensor.IsReindexing.comp`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Reindexing.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The composition of two maps satisfying `IsReindexing` also satisfies the `IsReindexing`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TensorSpecies TensorSpecies.Tensor in
open Module in
variable {C : Type} in
open Fin in
/-- The composition of two maps satisfying `IsReindexing` also satisfies the `IsReindexing`. -/
lemma TensorSpecies.Tensor.IsReindexing.comp {n n1 n2 : ℕ} {c : Fin n → C} {c1 : Fin n1 → C}
    {c2 : Fin n2 → C} {σ : Fin n1 → Fin n} {σ2 : Fin n2 → Fin n1}
    (h : IsReindexing c c1 σ) (h2 : IsReindexing c1 c2 σ2) : IsReindexing c c2 (σ ∘ σ2) :=
  ⟨h.1.comp h2.1, fun x => (h.2 (σ2 x)).trans (h2.2 x)⟩
