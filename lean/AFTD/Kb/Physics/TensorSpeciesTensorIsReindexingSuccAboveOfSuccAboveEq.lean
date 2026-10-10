import AFTD.Prelude
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexing
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingInjective
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingOnId
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingInvPerserveColor
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingToEquivSymmPerserveColor

/-!
# TensorSpecies.Tensor.IsReindexing.succAbove_of_succAbove_eq

Topic: special_relativity   Node: 18863c9d6dc6

Provenance: formalization of a published result. Source: Physlib, `TensorSpecies.Tensor.IsReindexing.succAbove_of_succAbove_eq`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Reindexing.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The conclusion of `succAbove` from an explicit survivor relabelling: if `σ'` fills the square `(σ i).succAbove ∘ σ' = σ ∘ i.succAbove`, carrying the complement of `i` to the complement of `σ i`, then it is a reindexing of the two shortened colour lists. The square forces `σ'` to be injective, hence bijective, so no bijectivity hypothesis is needed; this is why the statement is restricted to equal lengths. Where `succAbove` builds the relabelling from `σ` as a `dite` composite, the map here is the caller's, which is what lets it stand in the statement of a lemma the caller instantiates.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TensorSpecies TensorSpecies.Tensor TensorSpecies.Tensor.IsReindexing in
open Module in
variable {C : Type} in
open Fin in
/-- The conclusion of `succAbove` from an explicit survivor relabelling: if `σ'` fills the square `(σ i).succAbove ∘ σ' = σ ∘ i.succAbove`, carrying the complement of `i` to the complement of `σ i`, then it is a reindexing of the two shortened colour lists. The square forces `σ'` to be injective, hence bijective, so no bijectivity hypothesis is needed; this is why the statement is restricted to equal lengths. Where `succAbove` builds the relabelling from `σ` as a `dite` composite, the map here is the caller's, which is what lets it stand in the statement of a lemma the caller instantiates. -/
lemma TensorSpecies.Tensor.IsReindexing.succAbove_of_succAbove_eq {n : ℕ} {c c1 : Fin (n + 1) → C}
    {σ : Fin (n + 1) → Fin (n + 1)} {σ' : Fin n → Fin n} (i : Fin (n + 1))
    (h : IsReindexing c c1 σ) (hσ' : (σ i).succAbove ∘ σ' = σ ∘ i.succAbove) :
    IsReindexing (c ∘ (σ i).succAbove) (c1 ∘ i.succAbove) σ' := by
  have key : ∀ a, (σ i).succAbove (σ' a) = σ (i.succAbove a) := congrFun hσ'
  refine ⟨Finite.injective_iff_bijective.mp (fun a b hab => ?_), fun a => ?_⟩
  · exact Fin.succAbove_right_injective (h.injective (by rw [← key a, ← key b, hab]))
  · simpa only [Function.comp_apply, key a] using h.2 (i.succAbove a)
