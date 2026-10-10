import AFTD.Prelude
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexing
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingInjective
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingSurjective
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingPreserveColor
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingOnId
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingInvPerserveColor
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingToEquivSymmPerserveColor
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingSymm

/-!
# TensorSpecies.Tensor.IsReindexing.succAbove_of_neq_zero

Topic: special_relativity   Node: 687cc1de8efd

Provenance: formalization of a published result. Source: Physlib, `TensorSpecies.Tensor.IsReindexing.succAbove_of_neq_zero`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Reindexing.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a reindexing of `c` by `c1` via `σ` for which the index `i` is not sent to `0`, removing the `i`-th entry of `c1` and the `(σ i)`-th entry of `c` yields a reindexing of `c ∘ (σ i).succAbove` by `c1 ∘ i.succAbove` via the map `(σ i).pred.predAbove ∘ σ ∘ i.succAbove`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TensorSpecies TensorSpecies.Tensor TensorSpecies.Tensor.IsReindexing in
open Module in
variable {C : Type} in
open Fin in
/-- Given a reindexing of `c` by `c1` via `σ` for which the index `i` is not sent to `0`, removing the `i`-th entry of `c1` and the `(σ i)`-th entry of `c` yields a reindexing of `c ∘ (σ i).succAbove` by `c1 ∘ i.succAbove` via the map `(σ i).pred.predAbove ∘ σ ∘ i.succAbove`. -/
lemma TensorSpecies.Tensor.IsReindexing.succAbove_of_neq_zero {n n1 : ℕ} {c : Fin (n + 1) → C} {c1 : Fin (n1 + 1) → C}
    {σ : Fin (n1 + 1) → Fin (n + 1)} (i : Fin (n1 + 1))
    (h : IsReindexing c c1 σ) (hi : σ i ≠ 0) :
    IsReindexing (c ∘ (σ i).succAbove) (c1 ∘ i.succAbove)
      ((Fin.pred (σ i) hi).predAbove  ∘ σ ∘ i.succAbove) := by
  have hpr : σ i = ((σ i).pred hi).succ := (Fin.succ_pred _ _).symm
  have hne : ∀ x, σ (i.succAbove x) ≠ σ i := fun x heq =>
    Fin.succAbove_ne i x (h.injective heq)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro x1 x2 h2
    simp only [Function.comp_apply] at h2
    apply i.succAbove_right_injective (h.injective ?_)
    suffices h' :
        ((σ i).pred hi).succ.succAbove (((σ i).pred hi).predAbove (σ (i.succAbove x1))) =
        ((σ i).pred hi).succ.succAbove (((σ i).pred hi).predAbove (σ (i.succAbove x2))) by
      rwa [Fin.succ_succAbove_predAbove (hpr ▸ hne x1),
        Fin.succ_succAbove_predAbove (hpr ▸ hne x2)] at h'
    simpa using h2
  · intro k
    simp only [Function.comp_apply]
    suffices h' : ∃ a, σ (i.succAbove a) = (σ i).succAbove k by
      conv => enter [1, a]; rw [← ((σ i).pred hi).succ.succAbove_right_injective.eq_iff]
      obtain ⟨a, h'⟩ := h'
      exact ⟨a, by rw [Fin.succ_succAbove_predAbove (hpr ▸ hne a), ← hpr]; exact h'⟩
    obtain ⟨j, hj⟩ := h.surjective ((σ i).succAbove k)
    simp only [← hj, h.injective.eq_iff, Fin.exists_succAbove_eq_iff, ne_eq]
    rintro rfl
    simp at hj
  · intro x
    simp only [h.preserve_color, Function.comp_apply]
    congr 1
    conv_lhs => enter[1]; rw [hpr]
    exact Fin.succ_succAbove_predAbove (hpr ▸ hne x)
