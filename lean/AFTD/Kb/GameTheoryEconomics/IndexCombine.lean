import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalCard
import AFTD.Kb.GameTheoryEconomics.PrefixSum

/-!
# index_combine

Topic: general_equilibrium   Node: a298c19a4b6a

Provenance: formalization of a published result. Source: EconCSLib, `index_combine`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer_product.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Combine a block/index pair `(i, j)` back into a flat index.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Filter in
variable {I : Type*} [Fintype I] [DecidableEq I] [Inhabited I] [LinearOrder I] (card : I → ℕ+) in
/-- Combine a block/index pair `(i, j)` back into a flat index. -/
noncomputable def index_combine (p : Σ i, Fin (card i)) : Fin (total_card card) :=
  ⟨prefix_sum card p.1 + (p.2 : ℕ), by
    have h1 : prefix_sum card p.1 + (p.2 : ℕ) < prefix_sum card p.1 + (card p.1 : ℕ) := by
      simp only [add_lt_add_iff_left]
      exact p.2.is_lt
    have h2 : prefix_sum card p.1 + (card p.1 : ℕ) ≤ (total_card card : ℕ) := by
      simp only [prefix_sum, total_card]
      have h_subset : Finset.univ.filter (· ≤ p.1) ⊆ Finset.univ := Finset.filter_subset _ _
      have h_eq : (Finset.univ.filter (· ≤ p.1)).sum (fun j => (card j : ℕ)) =
                   (Finset.univ.filter (· < p.1)).sum (fun j => (card j : ℕ)) + (card p.1 : ℕ) := by
        have h_split : Finset.univ.filter (· ≤ p.1) = Finset.univ.filter (· < p.1) ∪ {p.1} := by
          ext j; simp [Finset.mem_filter, le_iff_lt_or_eq, or_comm]
        have h_disj : Disjoint (Finset.univ.filter (· < p.1)) {p.1} := by simp
        rw [h_split, Finset.sum_union h_disj, Finset.sum_singleton]
      rw [← h_eq]
      exact Finset.sum_le_sum_of_subset_of_nonneg h_subset (fun _ _ _ => by positivity)
    exact lt_of_lt_of_le h1 h2⟩
