import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.NumberTheory.PostageStampNumberNegTwoOfOddRepE
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.NumberTheory.IntMemHFoldSumset

/-!
# postage_stamp_number_neg_two_of_odd_family_e

Topic: elementary_number_theory   Node: 00e4b42d0854

Provenance: helper lemma. arXiv:2610.19470 (Positivity and negativity for h-bases for N), Theorem 4.1 and its proof

For h = 12r+5 (m = 6r+2), the set {-(2r+1), 2r+1, 4r+4} h-fold covers [0, 36r² + 48r + 12] = [0, n_h(2) - 2].
-/

theorem postage_stamp_number_neg_two_of_odd_family_e (r : ℕ) :
    ∀ n : ℕ, n ≤ 36 * r ^ 2 + 48 * r + 12 → int_mem_h_fold_sumset (12 * r + 5)
      {-(2 * (r : ℤ) + 1), 2 * (r : ℤ) + 1, 4 * (r : ℤ) + 4} (n : ℤ) := by
  intro n hn
  set q := n / (2 * r + 1) with hq
  set ρ := n % (2 * r + 1) with hρ
  have hnq0 : (2 * r + 1) * q + ρ = n := Nat.div_add_mod n (2 * r + 1)
  have hρw : ρ < 2 * r + 1 := Nat.mod_lt n (by omega)
  have hnq : (n : ℤ) = (2 * (r : ℤ) + 1) * (q : ℤ) + (ρ : ℤ) := by
    have : ((n : ℕ) : ℤ) = (((2 * r + 1) * q + ρ : ℕ) : ℤ) := by rw [hnq0]
    rw [this]; push_cast; ring
  have h1 : q ≤ 18 * r + 14 := by
    by_contra hc; push Not at hc
    have : (2 * r + 1) * (18 * r + 15) ≤ (2 * r + 1) * q := Nat.mul_le_mul_left _ hc
    nlinarith
  have h2 : q = 18 * r + 14 → ρ + 2 ≤ 2 * r := by
    intro hqe
    rw [hqe] at hnq0
    nlinarith
  have hρZ : (ρ : ℤ) < (2 * (r : ℤ) + 1) := by exact_mod_cast hρw
  have h1Z : (q : ℤ) ≤ 18 * (r : ℤ) + 14 := by exact_mod_cast h1
  have h2Z : (q : ℤ) = 18 * (r : ℤ) + 14 → (ρ : ℤ) + 2 ≤ 2 * (r : ℤ) := by
    intro h; exact_mod_cast h2 (by exact_mod_cast h)
  have h2D : (q : ℤ) < 18 * (r : ℤ) + 14 ∨ (ρ : ℤ) + 2 ≤ 2 * (r : ℤ) := by
    rcases lt_or_ge (q : ℤ) (18 * (r : ℤ) + 14) with hlt | hge
    · exact Or.inl hlt
    · exact Or.inr (h2Z (by omega))
  have h0D : 1 ≤ r ∨ q ≤ 12 := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · subst h0; right; omega
    · left; omega
  clear h2Z h2
  have hq0 : (0 : ℤ) ≤ q := Nat.cast_nonneg q
  have hρ0 : (0 : ℤ) ≤ ρ := Nat.cast_nonneg ρ
  have hr0 : (0 : ℤ) ≤ r := Nat.cast_nonneg r
  rcases (show (ρ : ℤ) % 2 = 0 ∨ (ρ : ℤ) % 2 = 1 by omega) with hε | hε
  · obtain ⟨u, hu⟩ : ∃ u : ℤ, 2 * u = (ρ : ℤ) + 0 * (2 * (r : ℤ) + 1) := ⟨(ρ : ℤ) / 2, by omega⟩
    rcases (show ((q : ℤ) - u - 0 - 1) % 2 = 0 ∨ ((q : ℤ) - u - 0 - 1) % 2 = 1 by omega) with hp | hp
    · by_cases hj0 : (q : ℤ) ≤ (12 * (r : ℤ) + 5) + 0 + 2 * 0 + u + 0 * (2 * (r : ℤ) + 1)
      · have := postage_stamp_number_neg_two_of_odd_rep_e r (u + 0 * (2 * (r : ℤ) + 1)) ((q : ℤ) - 0 - 2 * 0 - 2 * u - 2 * 0 * (2 * (r : ℤ) + 1)) (by omega) (by omega) (by omega) (by omega)
        have hv : (n : ℤ) = (2 * (r : ℤ) + 1) * ((q : ℤ) - 0 - 2 * 0 - 2 * u - 2 * 0 * (2 * (r : ℤ) + 1)) + (4 * (r : ℤ) + 4) * (u + 0 * (2 * (r : ℤ) + 1)) := by
          linear_combination hnq - hu
        rw [hv]; exact this
      by_cases hj1 : (q : ℤ) ≤ (12 * (r : ℤ) + 5) + 0 + 2 * 2 + u + 2 * (2 * (r : ℤ) + 1)
      · have := postage_stamp_number_neg_two_of_odd_rep_e r (u + 2 * (2 * (r : ℤ) + 1)) ((q : ℤ) - 0 - 2 * 2 - 2 * u - 2 * 2 * (2 * (r : ℤ) + 1)) (by omega) (by omega) (by omega) (by omega)
        have hv : (n : ℤ) = (2 * (r : ℤ) + 1) * ((q : ℤ) - 0 - 2 * 2 - 2 * u - 2 * 2 * (2 * (r : ℤ) + 1)) + (4 * (r : ℤ) + 4) * (u + 2 * (2 * (r : ℤ) + 1)) := by
          linear_combination hnq - hu
        rw [hv]; exact this
      have := postage_stamp_number_neg_two_of_odd_rep_e r (u + 4 * (2 * (r : ℤ) + 1)) ((q : ℤ) - 0 - 2 * 4 - 2 * u - 2 * 4 * (2 * (r : ℤ) + 1)) (by omega) (by omega) (by omega) (by omega)
      have hv : (n : ℤ) = (2 * (r : ℤ) + 1) * ((q : ℤ) - 0 - 2 * 4 - 2 * u - 2 * 4 * (2 * (r : ℤ) + 1)) + (4 * (r : ℤ) + 4) * (u + 4 * (2 * (r : ℤ) + 1)) := by
        linear_combination hnq - hu
      rw [hv]; exact this
    · by_cases hj0 : (q : ℤ) ≤ (12 * (r : ℤ) + 5) + 0 + 2 * 1 + u + 1 * (2 * (r : ℤ) + 1)
      · have := postage_stamp_number_neg_two_of_odd_rep_e r (u + 1 * (2 * (r : ℤ) + 1)) ((q : ℤ) - 0 - 2 * 1 - 2 * u - 2 * 1 * (2 * (r : ℤ) + 1)) (by omega) (by omega) (by omega) (by omega)
        have hv : (n : ℤ) = (2 * (r : ℤ) + 1) * ((q : ℤ) - 0 - 2 * 1 - 2 * u - 2 * 1 * (2 * (r : ℤ) + 1)) + (4 * (r : ℤ) + 4) * (u + 1 * (2 * (r : ℤ) + 1)) := by
          linear_combination hnq - hu
        rw [hv]; exact this
      by_cases hj1 : (q : ℤ) ≤ (12 * (r : ℤ) + 5) + 0 + 2 * 3 + u + 3 * (2 * (r : ℤ) + 1)
      · have := postage_stamp_number_neg_two_of_odd_rep_e r (u + 3 * (2 * (r : ℤ) + 1)) ((q : ℤ) - 0 - 2 * 3 - 2 * u - 2 * 3 * (2 * (r : ℤ) + 1)) (by omega) (by omega) (by omega) (by omega)
        have hv : (n : ℤ) = (2 * (r : ℤ) + 1) * ((q : ℤ) - 0 - 2 * 3 - 2 * u - 2 * 3 * (2 * (r : ℤ) + 1)) + (4 * (r : ℤ) + 4) * (u + 3 * (2 * (r : ℤ) + 1)) := by
          linear_combination hnq - hu
        rw [hv]; exact this
      have := postage_stamp_number_neg_two_of_odd_rep_e r (u + 5 * (2 * (r : ℤ) + 1)) ((q : ℤ) - 0 - 2 * 5 - 2 * u - 2 * 5 * (2 * (r : ℤ) + 1)) (by omega) (by omega) (by omega) (by omega)
      have hv : (n : ℤ) = (2 * (r : ℤ) + 1) * ((q : ℤ) - 0 - 2 * 5 - 2 * u - 2 * 5 * (2 * (r : ℤ) + 1)) + (4 * (r : ℤ) + 4) * (u + 5 * (2 * (r : ℤ) + 1)) := by
        linear_combination hnq - hu
      rw [hv]; exact this
  · obtain ⟨u, hu⟩ : ∃ u : ℤ, 2 * u = (ρ : ℤ) + 1 * (2 * (r : ℤ) + 1) := ⟨((ρ : ℤ) + (2 * (r : ℤ) + 1)) / 2, by omega⟩
    rcases (show ((q : ℤ) - u - 1 - 1) % 2 = 0 ∨ ((q : ℤ) - u - 1 - 1) % 2 = 1 by omega) with hp | hp
    · by_cases hj0 : (q : ℤ) ≤ (12 * (r : ℤ) + 5) + 1 + 2 * 0 + u + 0 * (2 * (r : ℤ) + 1)
      · have := postage_stamp_number_neg_two_of_odd_rep_e r (u + 0 * (2 * (r : ℤ) + 1)) ((q : ℤ) - 1 - 2 * 0 - 2 * u - 2 * 0 * (2 * (r : ℤ) + 1)) (by omega) (by omega) (by omega) (by omega)
        have hv : (n : ℤ) = (2 * (r : ℤ) + 1) * ((q : ℤ) - 1 - 2 * 0 - 2 * u - 2 * 0 * (2 * (r : ℤ) + 1)) + (4 * (r : ℤ) + 4) * (u + 0 * (2 * (r : ℤ) + 1)) := by
          linear_combination hnq - hu
        rw [hv]; exact this
      by_cases hj1 : (q : ℤ) ≤ (12 * (r : ℤ) + 5) + 1 + 2 * 2 + u + 2 * (2 * (r : ℤ) + 1)
      · have := postage_stamp_number_neg_two_of_odd_rep_e r (u + 2 * (2 * (r : ℤ) + 1)) ((q : ℤ) - 1 - 2 * 2 - 2 * u - 2 * 2 * (2 * (r : ℤ) + 1)) (by omega) (by omega) (by omega) (by omega)
        have hv : (n : ℤ) = (2 * (r : ℤ) + 1) * ((q : ℤ) - 1 - 2 * 2 - 2 * u - 2 * 2 * (2 * (r : ℤ) + 1)) + (4 * (r : ℤ) + 4) * (u + 2 * (2 * (r : ℤ) + 1)) := by
          linear_combination hnq - hu
        rw [hv]; exact this
      have := postage_stamp_number_neg_two_of_odd_rep_e r (u + 4 * (2 * (r : ℤ) + 1)) ((q : ℤ) - 1 - 2 * 4 - 2 * u - 2 * 4 * (2 * (r : ℤ) + 1)) (by omega) (by omega) (by omega) (by omega)
      have hv : (n : ℤ) = (2 * (r : ℤ) + 1) * ((q : ℤ) - 1 - 2 * 4 - 2 * u - 2 * 4 * (2 * (r : ℤ) + 1)) + (4 * (r : ℤ) + 4) * (u + 4 * (2 * (r : ℤ) + 1)) := by
        linear_combination hnq - hu
      rw [hv]; exact this
    · by_cases hj0 : (q : ℤ) ≤ (12 * (r : ℤ) + 5) + 1 + 2 * 1 + u + 1 * (2 * (r : ℤ) + 1)
      · have := postage_stamp_number_neg_two_of_odd_rep_e r (u + 1 * (2 * (r : ℤ) + 1)) ((q : ℤ) - 1 - 2 * 1 - 2 * u - 2 * 1 * (2 * (r : ℤ) + 1)) (by omega) (by omega) (by omega) (by omega)
        have hv : (n : ℤ) = (2 * (r : ℤ) + 1) * ((q : ℤ) - 1 - 2 * 1 - 2 * u - 2 * 1 * (2 * (r : ℤ) + 1)) + (4 * (r : ℤ) + 4) * (u + 1 * (2 * (r : ℤ) + 1)) := by
          linear_combination hnq - hu
        rw [hv]; exact this
      by_cases hj1 : (q : ℤ) ≤ (12 * (r : ℤ) + 5) + 1 + 2 * 3 + u + 3 * (2 * (r : ℤ) + 1)
      · have := postage_stamp_number_neg_two_of_odd_rep_e r (u + 3 * (2 * (r : ℤ) + 1)) ((q : ℤ) - 1 - 2 * 3 - 2 * u - 2 * 3 * (2 * (r : ℤ) + 1)) (by omega) (by omega) (by omega) (by omega)
        have hv : (n : ℤ) = (2 * (r : ℤ) + 1) * ((q : ℤ) - 1 - 2 * 3 - 2 * u - 2 * 3 * (2 * (r : ℤ) + 1)) + (4 * (r : ℤ) + 4) * (u + 3 * (2 * (r : ℤ) + 1)) := by
          linear_combination hnq - hu
        rw [hv]; exact this
      have := postage_stamp_number_neg_two_of_odd_rep_e r (u + 5 * (2 * (r : ℤ) + 1)) ((q : ℤ) - 1 - 2 * 5 - 2 * u - 2 * 5 * (2 * (r : ℤ) + 1)) (by omega) (by omega) (by omega) (by omega)
      have hv : (n : ℤ) = (2 * (r : ℤ) + 1) * ((q : ℤ) - 1 - 2 * 5 - 2 * u - 2 * 5 * (2 * (r : ℤ) + 1)) + (4 * (r : ℤ) + 4) * (u + 5 * (2 * (r : ℤ) + 1)) := by
        linear_combination hnq - hu
      rw [hv]; exact this
