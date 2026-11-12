import AFTD.Prelude

/-!
# scalar_sampler_m_pairwise_coprime

Topic: information   Node: 606485b400f2

Provenance: helper lemma. arXiv:2611.13281, Section 2, equation (1)

For integers q ≥ 3 and r ≥ 1, the parameters m_j = 1 + (q-1)!(12r(q-1) + j) for 0 ≤ j < q are pairwise coprime.
-/

/-- The moduli m_j = 1 + (q-1)!(12r(q-1) + j) are pairwise coprime for 0 ≤ j < q. -/
theorem scalar_sampler_m_pairwise_coprime (q r : ℕ) (hq : 3 ≤ q) (hr : 1 ≤ r)
    {j k : ℕ} (hj : j < q) (hk : k < q) (hjk : j ≠ k) :
    let m : ℕ → ℤ := fun i => 1 + (q - 1).factorial * (12 * r * (q - 1) + i)
    Nat.Coprime (m j).natAbs (m k).natAbs := by
  have _ := hr
  intro m
  apply Nat.coprime_of_dvd
  intro p hp hj_dvd hk_dvd
  have hj_int : (p : ℤ) ∣ m j := Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hj_dvd)
  have hk_int : (p : ℤ) ∣ m k := Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr hk_dvd)
  have hdiff_int : (p : ℤ) ∣ m j - m k := dvd_sub hj_int hk_int
  have hm : m j - m k = ((q - 1).factorial : ℤ) * ((j : ℤ) - (k : ℤ)) := by
    dsimp [m]
    ring
  rw [hm] at hdiff_int
  have hdvd : p ∣ (((q - 1).factorial : ℤ) * ((j : ℤ) - (k : ℤ))).natAbs := by
    rw [← Int.natCast_dvd_natCast, Int.natCast_natAbs, dvd_abs]
    exact hdiff_int
  rw [Int.natAbs_mul, Int.natAbs_natCast] at hdvd
  have hp_fac : p ∣ (q - 1).factorial := by
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h1 | h2
    · exact h1
    · have h_pos : 0 < ((j : ℤ) - (k : ℤ)).natAbs := by omega
      have h_le : ((j : ℤ) - (k : ℤ)).natAbs ≤ q - 1 := by omega
      have hp_le : p ≤ q - 1 := (Nat.le_of_dvd h_pos h2).trans h_le
      exact (Nat.Prime.dvd_factorial hp).mpr hp_le
  have hfac_int : (p : ℤ) ∣ ((q - 1).factorial : ℤ) := Int.natCast_dvd_natCast.mpr hp_fac
  have h_prod : (p : ℤ) ∣ ((q - 1).factorial : ℤ) * (12 * r * (q - 1) + k) :=
    dvd_mul_of_dvd_left hfac_int _
  have h1 : (p : ℤ) ∣ m k - ((q - 1).factorial : ℤ) * (12 * r * (q - 1) + k) :=
    dvd_sub hk_int h_prod
  have hm1 : m k - ((q - 1).factorial : ℤ) * (12 * r * (q - 1) + k) = 1 := by
    dsimp [m]
    ring
  rw [hm1] at h1
  have hp_dvd_one : p ∣ 1 := Int.natCast_dvd_natCast.mp h1
  exact hp.not_dvd_one hp_dvd_one
