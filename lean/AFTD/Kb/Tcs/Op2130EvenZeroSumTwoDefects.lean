import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# op_2130_even_zero_sum_two_defects

Topic: online_algorithms   Node: 86700a008bcf

Provenance: helper lemma. OP-2130: synchronized greedy coupling cannot branch a single coin perturbation

A finite integer vector with even coordinates, zero sum, and squared norm at most eight is zero or has exactly one coordinate equal to two and exactly one equal to minus two.
-/

theorem op_2130_even_zero_sum_two_defects (n : ℕ) (f : Fin n → ℤ) (heven : ∀ i, Even (f i)) (hsum : (∑ i, f i) = 0) (hnorm : (∑ i, (f i)^2) ≤ 8) : (∀ i, f i = 0) ∨ ∃ a b : Fin n, a ≠ b ∧ f a = 2 ∧ f b = -2 ∧ ∀ i, i ≠ a → i ≠ b → f i = 0 := by
  have hsq_le : ∀ i, (f i)^2 ≤ 8 := by
    intro i
    have h := Finset.single_le_sum (s := Finset.univ) (f := fun j => (f j)^2)
      (fun j _ => sq_nonneg (f j)) (Finset.mem_univ i)
    simpa using h.trans hnorm
  have hcoord : ∀ i, f i = 0 ∨ f i = 2 ∨ f i = -2 := by
    intro i
    obtain ⟨k, hk⟩ := heven i
    have hx : f i = 2 * k := by rw [hk, two_mul]
    have hsi : (f i)^2 ≤ 8 := hsq_le i
    rw [hx] at hsi
    have hk2 : k^2 ≤ 2 := by nlinarith
    have hk_low : -1 ≤ k := by nlinarith [sq_nonneg (k+1 : ℤ)]
    have hk_high : k ≤ 1 := by nlinarith [sq_nonneg (k-1 : ℤ)]
    rw [hx]
    interval_cases k <;> simp
  let nz : Finset (Fin n) := Finset.univ.filter (fun i => f i ≠ 0)
  have hnz_sq : ∀ i ∈ nz, (f i)^2 = 4 := by
    intro i hi
    have hneq : f i ≠ 0 := by simpa [nz] using hi
    rcases hcoord i with h0 | h2 | hm2
    · exact absurd h0 hneq
    · simp [h2]
    · simp [hm2]
  have hsum_sq_nz : (∑ i ∈ nz, (f i)^2) = 4 * (nz.card : ℤ) := by
    calc
      (∑ i ∈ nz, (f i)^2) = ∑ i ∈ nz, (4 : ℤ) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hnz_sq i hi
      _ = 4 * (nz.card : ℤ) := by simp [mul_comm]
  have hsum_sq_univ : (∑ i, (f i)^2) = ∑ i ∈ nz, (f i)^2 := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : f i = 0
    · simp [h]
    · simp [h]
  have hcard_le : nz.card ≤ 2 := by
    have h : 4 * (nz.card : ℤ) ≤ 8 := by
      rw [← hsum_sq_nz, ← hsum_sq_univ]
      exact hnorm
    have h' : (nz.card : ℤ) ≤ 2 := by linarith
    omega
  interval_cases hc : nz.card
  · left
    intro i
    have hi : i ∉ nz := by
      rw [Finset.card_eq_zero] at hc
      rw [hc]
      simp
    simpa [nz] using hi
  · exfalso
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
    have hsum_nz : (∑ i, f i) = ∑ i ∈ nz, f i := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : f i = 0
      · simp [h]
      · simp [h]
    have hfa : f a = 0 := by
      rw [hsum_nz, ha] at hsum
      simpa using hsum
    have : a ∈ nz := by rw [ha]; simp
    have hne : f a ≠ 0 := by simpa [nz] using this
    exact hne hfa
  · right
    obtain ⟨a, b, hab, hset⟩ := Finset.card_eq_two.mp hc
    have hsum_nz : (∑ i, f i) = ∑ i ∈ nz, f i := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases h : f i = 0
      · simp [h]
      · simp [h]
    have hfab : f a + f b = 0 := by
      rw [hsum_nz, hset] at hsum
      rw [Finset.sum_pair hab] at hsum
      simpa using hsum
    have ha_mem : a ∈ nz := by rw [hset]; simp
    have hb_mem : b ∈ nz := by rw [hset]; simp
    have ha_ne : f a ≠ 0 := by simpa [nz] using ha_mem
    have hb_ne : f b ≠ 0 := by simpa [nz] using hb_mem
    rcases hcoord a with ha0 | ha2 | ham2
    · exact absurd ha0 ha_ne
    · have hb2 : f b = -2 := by linarith
      refine ⟨a, b, hab, ha2, hb2, ?_⟩
      intro i hia hib
      have hin : i ∉ nz := by
        rw [hset]
        simp [hia, hib]
      simpa [nz] using hin
    · have hb2 : f b = 2 := by linarith
      refine ⟨b, a, hab.symm, hb2, ham2, ?_⟩
      intro i hib hia
      have hin : i ∉ nz := by
        rw [hset]
        simp [hia, hib]
      simpa [nz] using hin
