import AFTD.Prelude

/-!
# weighted_harmonic_ratio_le_one_iff

Topic: general_equilibrium   Node: 7fd385f804b3

Provenance: helper lemma. arXiv:2610.29731 Lemma 4 proof

For any finite nonempty set of components with positive weights W_j > 0 and ratios r_j in (0, 1], the ratio α* = (∑_j W_j) / (∑_j W_j / r_j) satisfies α* ≤ 1, with equality if and only if r_j = 1 for all j.
-/

/-- A weighted harmonic-type ratio with positive weights W_j and multipliers r_j in (0, 1] is at most 1, with equality iff all r_j = 1. -/
theorem weighted_harmonic_ratio_le_one_iff
    {M : Type*} [Fintype M] [Nonempty M]
    (W : M → ℝ) (r : M → ℝ)
    (hW : ∀ j, 0 < W j)
    (hr_pos : ∀ j, 0 < r j)
    (hr_le : ∀ j, r j ≤ 1) :
    let W_bar := Finset.univ.sum W
    let α_star := W_bar / Finset.univ.sum (fun j => W j / r j)
    α_star ≤ 1 ∧ (α_star = 1 ↔ ∀ j, r j = 1) := by
  intro W_bar α_star
  have h_denom_pos : 0 < ∑ j, W j / r j :=
    Finset.sum_pos (fun j _ => div_pos (hW j) (hr_pos j)) Finset.univ_nonempty
  have h_le_term : ∀ j, W j ≤ W j / r j := by
    intro j
    exact (le_div_iff₀ (hr_pos j)).mpr (by nlinarith [hW j, hr_le j])
  have h_le_sum : W_bar ≤ ∑ j, W j / r j :=
    Finset.sum_le_sum (fun j _ => h_le_term j)
  have h_le_one : α_star ≤ 1 :=
    (div_le_one₀ h_denom_pos).mpr h_le_sum
  refine ⟨h_le_one, ⟨?_, ?_⟩⟩
  · intro hα
    have h_sum_eq : W_bar = ∑ j, W j / r j :=
      (div_eq_one_iff_eq (ne_of_gt h_denom_pos)).mp hα
    have h_diff_zero : ∑ j, (W j / r j - W j) = 0 := by
      rw [Finset.sum_sub_distrib]
      change (∑ j, W j / r j) - W_bar = 0
      rw [← h_sum_eq, sub_self]
    have h_term_nonneg : ∀ j ∈ (Finset.univ : Finset M), 0 ≤ W j / r j - W j := by
      intro j _
      have := h_le_term j
      linarith
    have h_each_zero := (Finset.sum_eq_zero_iff_of_nonneg h_term_nonneg).mp h_diff_zero
    intro j
    have hj_zero : W j / r j - W j = 0 := h_each_zero j (Finset.mem_univ j)
    have hj_eq : W j / r j = W j := by linarith
    have h1 : (W j / r j) * r j = W j * r j := by rw [hj_eq]
    rw [div_mul_cancel₀ (W j) (ne_of_gt (hr_pos j))] at h1
    have h2 : W j * r j = W j * 1 := by rw [← h1, mul_one]
    exact mul_left_cancel₀ (ne_of_gt (hW j)) h2
  · intro hr_one
    have h_eq : (∑ j, W j / r j) = W_bar := by
      dsimp [W_bar]
      simp_rw [hr_one, div_one]
    dsimp [α_star]
    rw [h_eq]
    have hW_bar_pos : 0 < W_bar :=
      Finset.sum_pos (fun j _ => hW j) Finset.univ_nonempty
    exact div_self (ne_of_gt hW_bar_pos)
