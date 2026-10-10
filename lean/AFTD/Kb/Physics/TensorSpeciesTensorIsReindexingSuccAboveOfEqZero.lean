import AFTD.Prelude
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexing
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingInjective
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingSurjective
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingPreserveColor
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingOnId
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingInvPerserveColor
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingToEquivSymmPerserveColor

/-!
# TensorSpecies.Tensor.IsReindexing.succAbove_of_eq_zero

Topic: special_relativity   Node: e16a48d42f32

Provenance: formalization of a published result. Source: Physlib, `TensorSpecies.Tensor.IsReindexing.succAbove_of_eq_zero`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Reindexing.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a reindexing of `c` by `c1` via `σ` for which the index `i` is sent to `0`, removing the `i`-th entry of `c1` and the first entry of `c` yields a reindexing of `c ∘ Fin.succ` by `c1 ∘ i.succAbove` via the map sending `j` to the predecessor of `σ (i.succAbove j)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TensorSpecies TensorSpecies.Tensor TensorSpecies.Tensor.IsReindexing in
open Module in
variable {C : Type} in
open Fin in
/-- Given a reindexing of `c` by `c1` via `σ` for which the index `i` is sent to `0`, removing the `i`-th entry of `c1` and the first entry of `c` yields a reindexing of `c ∘ Fin.succ` by `c1 ∘ i.succAbove` via the map sending `j` to the predecessor of `σ (i.succAbove j)`. -/
lemma TensorSpecies.Tensor.IsReindexing.succAbove_of_eq_zero {n n1 : ℕ} {c : Fin (n + 1) → C} {c1 : Fin (n1 + 1) → C}
    {σ : Fin (n1 + 1) → Fin (n + 1)} (i : Fin (n1 + 1))
    (h : IsReindexing c c1 σ) (hi : σ i = 0) :
    IsReindexing (c ∘ Fin.succ) (c1 ∘ i.succAbove)
      (fun j => (σ (i.succAbove j)).pred (by simp [← hi, h.injective.eq_iff])) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro x1 x2 h1
    simpa [h.injective.eq_iff] using h1
  · intro k
    suffices ha : ∃ a, σ (i.succAbove a) = k.succ by
      obtain ⟨a, ha⟩ := ha
      use a
      simp [ha]
    obtain ⟨j, hj⟩ := h.surjective k.succ
    simp only [← hj, h.injective.eq_iff, Fin.exists_succAbove_eq_iff, ne_eq]
    grind
  · intro x
    simp [h.preserve_color]
