import AFTD.Prelude
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexing
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingSuccAboveOfEqZero
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingSuccAboveOfNeqZero
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingOnId
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingInvPerserveColor
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingToEquivSymmPerserveColor
import AFTD.Kb.Physics.TensorSpeciesTensorIsReindexingInjective

/-!
# TensorSpecies.Tensor.IsReindexing.succAbove

Topic: special_relativity   Node: 95fa65f14d67

Provenance: formalization of a published result. Source: Physlib, `TensorSpecies.Tensor.IsReindexing.succAbove`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Reindexing.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a reindexing of `c` by `c1` via `σ`, removing the `i`-th entry of `c1` and the `(σ i)`-th entry of `c` yields a reindexing of `c ∘ (σ i).succAbove` by `c1 ∘ i.succAbove`. This unifies `succAbove_of_eq_zero` and `succAbove_of_neq_zero` via a case split on whether `σ i = 0`. This is used for the commutation of *permutation* of indices with *evaluation* of indices.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open TensorSpecies TensorSpecies.Tensor TensorSpecies.Tensor.IsReindexing in
open Module in
variable {C : Type} in
open Fin in
/-- Given a reindexing of `c` by `c1` via `σ`, removing the `i`-th entry of `c1` and the `(σ i)`-th entry of `c` yields a reindexing of `c ∘ (σ i).succAbove` by `c1 ∘ i.succAbove`. This unifies `succAbove_of_eq_zero` and `succAbove_of_neq_zero` via a case split on whether `σ i = 0`. This is used for the commutation of *permutation* of indices with *evaluation* of indices. -/
lemma TensorSpecies.Tensor.IsReindexing.succAbove {n n1 : ℕ} {c : Fin (n + 1) → C} {c1 : Fin (n1 + 1) → C}
    {σ : Fin (n1 + 1) → Fin (n + 1)} (i : Fin (n1 + 1))
    (h : IsReindexing c c1 σ) :
    IsReindexing (c ∘ (σ i).succAbove) (c1 ∘ i.succAbove)
      (if hi : σ i = 0 then fun j => (σ (i.succAbove j)).pred (by simp [← hi, h.injective.eq_iff])
      else (Fin.pred (σ i) hi).predAbove  ∘ σ ∘ i.succAbove) := by
  by_cases hi : σ i = 0
  · simpa [hi] using IsReindexing.succAbove_of_eq_zero i h hi
  · simpa [hi] using IsReindexing.succAbove_of_neq_zero i h hi
