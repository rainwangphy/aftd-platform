import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalCard
import AFTD.Kb.GameTheoryEconomics.PrefixSum

/-!
# index_split_existence

Topic: general_equilibrium   Node: 336ca434f360

Provenance: formalization of a published result. Source: EconCSLib, `index_split_existence`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Brouwer_product.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

A flat index `k` belongs to a unique block `i` with an in-block index `j`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Filter in
variable {I : Type*} [Fintype I] [DecidableEq I] [Inhabited I] [LinearOrder I] (card : I → ℕ+) in
/-- A flat index `k` belongs to a unique block `i` with an in-block index `j`. -/
lemma index_split_existence (k : Fin (total_card card)) : ∃ (p : Σ i, Fin (card i)),
    prefix_sum card p.1 ≤ k.val ∧ k.val < prefix_sum card p.1 + (card p.1 : ℕ) ∧
    p.2.val = k.val - prefix_sum card p.1 := by
  let prefix_sum_inclusive (i : I) : ℕ := ∑ j ∈ Finset.univ.filter (· ≤ i), (card j : ℕ)
  let S : Set I := {i | k.val < prefix_sum_inclusive i}
  have s_nonempty : S.Nonempty := by
    let i_max := (Finset.univ : Finset I).max' Finset.univ_nonempty
    use i_max
    have h_sum_eq_total : prefix_sum_inclusive i_max = (total_card card : ℕ) := by
      simp only [prefix_sum_inclusive, total_card]
      rw [Finset.filter_true_of_mem]
      simp
      intro j _; exact Finset.le_max' _ _ (Finset.mem_univ j)
    show k.val < prefix_sum_inclusive i_max
    rw [h_sum_eq_total]
    exact k.is_lt
  let i₀ := @WellFounded.min I (· < ·) wellFounded_lt S s_nonempty
  have i₀_in_S : i₀ ∈ S := WellFounded.min_mem wellFounded_lt S s_nonempty
  have i₀_is_min : ∀ j < i₀, j ∉ S := fun j hlt => by
    intro hj
    have := WellFounded.min_le wellFounded_lt hj
    exact not_le_of_gt hlt this
  have h_lt : k.val < prefix_sum card i₀ + (card i₀ : ℕ) := by
    try simp at i₀_in_S
    change k.val < (∑ j ∈ Finset.univ.filter (· ≤ i₀), (card j : ℕ)) at i₀_in_S
    have : (∑ j ∈ Finset.univ.filter (· ≤ i₀), (card j : ℕ)) =
            (∑ j ∈ Finset.univ.filter (· < i₀), (card j : ℕ)) + (card i₀ : ℕ) := by
      have h_split : Finset.univ.filter (· ≤ i₀) = Finset.univ.filter (· < i₀) ∪ {i₀} := by
        ext j
        simp [le_iff_lt_or_eq, or_comm]
      rw [h_split, Finset.sum_union]
      · simp
      · simp
    rwa [this] at i₀_in_S
  have h_le : prefix_sum card i₀ ≤ k.val := by
    by_cases h_i₀_is_min : i₀ = (Finset.univ.min' Finset.univ_nonempty)
    · rw [h_i₀_is_min, prefix_sum]
      rw [Finset.sum_eq_zero]
      · exact Nat.zero_le _
      · intro j hj
        simp only [Finset.mem_filter] at hj
        exact False.elim (not_lt_of_ge (Finset.min'_le _ _ (Finset.mem_univ j)) hj.2)
    · let pred_set := Finset.univ.filter (· < i₀)
      have pred_set_nonempty : pred_set.Nonempty := by
        have : i₀ ≠ Finset.univ.min' Finset.univ_nonempty := h_i₀_is_min
        have : ¬ (∀ j ∈ Finset.univ, i₀ ≤ j) := by
          intro h_all_ge
          have h_min : i₀ = Finset.univ.min' Finset.univ_nonempty := by
            apply le_antisymm
            · exact h_all_ge (Finset.univ.min' Finset.univ_nonempty) (Finset.mem_univ _)
            · exact Finset.min'_le _ _ (Finset.mem_univ i₀)
          exact this h_min
        push_neg at this
        obtain ⟨j, _, hj⟩ := this
        exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
      let j₀ := pred_set.max' pred_set_nonempty
      have j₀_lt_i₀ : j₀ < i₀ := by
        have h_mem : j₀ ∈ pred_set := Finset.max'_mem pred_set pred_set_nonempty
        exact (Finset.mem_filter.mp h_mem).2
      have j₀_notin_S : j₀ ∉ S := i₀_is_min j₀ j₀_lt_i₀
      have j₀_ineq : prefix_sum_inclusive j₀ ≤ k.val := by
        simp only [S, Set.mem_setOf_eq] at j₀_notin_S
        exact le_of_not_gt j₀_notin_S
      have : prefix_sum card i₀ = prefix_sum_inclusive j₀ := by
        simp only [prefix_sum, prefix_sum_inclusive]
        congr 1
        ext x
        simp only [Finset.mem_filter]
        apply Iff.intro
        · intro h_x_lt_i₀
          exact ⟨Finset.mem_univ x, Finset.le_max' pred_set x (Finset.mem_filter.mpr h_x_lt_i₀)⟩
        · intro h_x_le_j₀
          exact ⟨Finset.mem_univ x, lt_of_le_of_lt h_x_le_j₀.2 j₀_lt_i₀⟩
      exact this ▸ j₀_ineq
  use { fst := i₀, snd := ⟨k.val - prefix_sum card i₀, by
    rw [Nat.sub_lt_iff_lt_add h_le]; rwa [add_comm]⟩ }
