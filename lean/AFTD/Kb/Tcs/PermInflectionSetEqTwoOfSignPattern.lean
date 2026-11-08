import AFTD.Prelude
import AFTD.Kb.Tcs.PermSecondDerivative
import AFTD.Kb.Tcs.PermInflectionSet
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# perm_inflection_set_eq_two_of_sign_pattern

Topic: combinatorics   Node: b67793eafe97

Provenance: helper lemma. step towards op_686_disjoint_two_element_inflection_set_admissible

If a permutation σ has discrete second derivative that is non-negative on [2, k₁), positive at k₁, zero on (k₁, m₁), negative at m₁, non-positive on (m₁, k₂), negative at k₂, zero on (k₂, m₂), positive at m₂, and non-negative on (m₂, n-1], then perm_inflection_set σ = {(k₁, m₁), (k₂, m₂)}.
-/

/-- If a permutation's discrete second derivative satisfies the 2-inflection sign pattern, its inflection set is exactly {(k₁, m₁), (k₂, m₂)}. -/
theorem perm_inflection_set_eq_two_of_sign_pattern
    {n : ℕ} (σ : Equiv.Perm (Fin n)) (k₁ m₁ k₂ m₂ : ℕ)
    (hk1 : 2 ≤ k₁) (h1 : k₁ < m₁) (h12 : m₁ < k₂) (h2 : k₂ < m₂) (hm2n : m₂ ≤ n - 1)
    (h_pos_k1 : 0 < perm_second_derivative σ k₁)
    (h_zero_1 : ∀ ℓ ∈ Finset.Ioo k₁ m₁, perm_second_derivative σ ℓ = 0)
    (h_neg_m1 : perm_second_derivative σ m₁ < 0)
    (h_nonpos_mid : ∀ ℓ ∈ Finset.Ioo m₁ k₂, perm_second_derivative σ ℓ ≤ 0)
    (h_neg_k2 : perm_second_derivative σ k₂ < 0)
    (h_zero_2 : ∀ ℓ ∈ Finset.Ioo k₂ m₂, perm_second_derivative σ ℓ = 0)
    (h_pos_m2 : 0 < perm_second_derivative σ m₂)
    (h_nonneg_pre : ∀ ℓ ∈ Finset.Ico 2 k₁, 0 ≤ perm_second_derivative σ ℓ)
    (h_nonneg_post : ∀ ℓ ∈ Finset.Ioc m₂ (n - 1), 0 ≤ perm_second_derivative σ ℓ) :
    perm_inflection_set σ = {(k₁, m₁), (k₂, m₂)} := by
  have h_le_zero : ∀ ℓ, k₁ < ℓ → ℓ < m₂ → perm_second_derivative σ ℓ ≤ 0 := by
    intro ℓ hk hmm2
    by_cases hℓm1 : ℓ < m₁
    · have hmem : ℓ ∈ Finset.Ioo k₁ m₁ := by simp only [Finset.mem_Ioo]; exact ⟨hk, hℓm1⟩
      rw [h_zero_1 ℓ hmem]
    · by_cases hℓe : ℓ = m₁
      · subst hℓe; exact le_of_lt h_neg_m1
      · have hm1ℓ : m₁ < ℓ := by omega
        by_cases hℓk2 : ℓ < k₂
        · exact h_nonpos_mid ℓ (by simp only [Finset.mem_Ioo]; exact ⟨hm1ℓ, hℓk2⟩)
        · by_cases hℓe2 : ℓ = k₂
          · subst hℓe2; exact le_of_lt h_neg_k2
          · have hk2ℓ : k₂ < ℓ := by omega
            have hmem : ℓ ∈ Finset.Ioo k₂ m₂ := by simp only [Finset.mem_Ioo]; exact ⟨hk2ℓ, hmm2⟩
            rw [h_zero_2 ℓ hmem]
  have h_nonneg_before : ∀ ℓ, 2 ≤ ℓ → ℓ < m₁ → 0 ≤ perm_second_derivative σ ℓ := by
    intro ℓ h2ℓ hℓm1
    by_cases hℓk1 : ℓ < k₁
    · exact h_nonneg_pre ℓ (by simp only [Finset.mem_Ico]; exact ⟨h2ℓ, hℓk1⟩)
    · by_cases hℓe : ℓ = k₁
      · subst hℓe; exact le_of_lt h_pos_k1
      · have hk1ℓ : k₁ < ℓ := by omega
        have hmem : ℓ ∈ Finset.Ioo k₁ m₁ := by simp only [Finset.mem_Ioo]; exact ⟨hk1ℓ, hℓm1⟩
        rw [h_zero_1 ℓ hmem]
  have h_nonneg_after : ∀ ℓ, k₂ < ℓ → ℓ ≤ n - 1 → 0 ≤ perm_second_derivative σ ℓ := by
    intro ℓ hk2ℓ hℓn
    by_cases hℓm2 : ℓ < m₂
    · have hmem : ℓ ∈ Finset.Ioo k₂ m₂ := by simp only [Finset.mem_Ioo]; exact ⟨hk2ℓ, hℓm2⟩
      rw [h_zero_2 ℓ hmem]
    · by_cases hℓe : ℓ = m₂
      · subst hℓe; exact le_of_lt h_pos_m2
      · have hm2ℓ : m₂ < ℓ := by omega
        exact h_nonneg_post ℓ (by simp only [Finset.mem_Ioc]; exact ⟨hm2ℓ, hℓn⟩)
  have key_pos : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ n - 1 → 0 < perm_second_derivative σ ℓ → ℓ ≤ k₁ ∨ m₂ ≤ ℓ := by
    intro ℓ h2ℓ hℓn hpos
    by_contra hc
    push Not at hc
    have := h_le_zero ℓ hc.1 hc.2
    linarith
  have key_neg : ∀ ℓ, 2 ≤ ℓ → ℓ ≤ n - 1 → perm_second_derivative σ ℓ < 0 → m₁ ≤ ℓ ∧ ℓ ≤ k₂ := by
    intro ℓ h2ℓ hℓn hneg
    constructor
    · by_contra hc; push Not at hc
      have := h_nonneg_before ℓ h2ℓ hc
      linarith
    · by_contra hc; push Not at hc
      have := h_nonneg_after ℓ hc hℓn
      linarith
  ext x
  obtain ⟨m, p⟩ := x
  simp only [perm_inflection_set, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
    Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨⟨hm2, hmn1⟩, hp2, hpn1⟩, hlt, hprod, hzero⟩
    rcases Int.mul_neg_iff.mp hprod with ⟨hmp, hpp⟩ | ⟨hmp, hpp⟩
    · -- 0 < d m, d p < 0  →  (k₁, m₁)
      obtain ⟨hm1p, hpk2⟩ := key_neg p hp2 hpn1 hpp
      rcases key_pos m hm2 hmn1 hmp with hmk1 | hm2m
      · have hmk1' : m = k₁ := by
          by_contra hc
          have hltk : m < k₁ := by omega
          have := hzero k₁ (by simp only [Finset.mem_Ioo]; exact ⟨hltk, by omega⟩)
          linarith
        have hpm1' : p = m₁ := by
          by_contra hc
          have hltm : m₁ < p := by omega
          have := hzero m₁ (by simp only [Finset.mem_Ioo]; exact ⟨by omega, hltm⟩)
          linarith
        exact Or.inl ⟨hmk1', hpm1'⟩
      · omega
    · -- d m < 0, 0 < d p  →  (k₂, m₂)
      obtain ⟨hm1m, hmk2⟩ := key_neg m hm2 hmn1 hmp
      rcases key_pos p hp2 hpn1 hpp with hpk1 | hpm2
      · omega
      · have hpm2' : p = m₂ := by
          by_contra hc
          have hltm : m₂ < p := by omega
          have := hzero m₂ (by simp only [Finset.mem_Ioo]; exact ⟨by omega, hltm⟩)
          linarith
        have hmk2' : m = k₂ := by
          by_contra hc
          have hltk : m < k₂ := by omega
          have := hzero k₂ (by simp only [Finset.mem_Ioo]; exact ⟨hltk, by omega⟩)
          linarith
        exact Or.inr ⟨hmk2', hpm2'⟩
  · rintro (⟨hmk1, hpm1⟩ | ⟨hmk2, hpm2⟩)
    · rw [hmk1, hpm1]
      exact ⟨⟨⟨hk1, by omega⟩, by omega, by omega⟩, h1,
        mul_neg_of_pos_of_neg h_pos_k1 h_neg_m1, h_zero_1⟩
    · rw [hmk2, hpm2]
      exact ⟨⟨⟨by omega, by omega⟩, by omega, hm2n⟩, h2,
        mul_neg_of_neg_of_pos h_neg_k2 h_pos_m2, h_zero_2⟩
