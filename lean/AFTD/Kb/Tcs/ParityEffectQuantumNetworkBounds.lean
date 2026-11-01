import AFTD.Prelude
import AFTD.Kb.Tcs.ClosedNetworkBound
import AFTD.Kb.Tcs.OpenNetworkBound
import AFTD.Kb.Tcs.ConcavePowerSumLe

/-!
# parity_effect_quantum_network_bounds

Topic: quantum   Node: 057546443237

Provenance: formalization of a published result. Source: arXiv:2610.35838 Theorem 4

For every natural number n with 1 <= n, and all real numbers p, q with 0 <= p, 0 <= q, p <= 1, and q <= 1, if ¬ Even n implies p^2 + q^2 <= 1, then Real.sqrt (p ^ (2 / (n : ℝ)) + q ^ (2 / (n : ℝ))) ≤ closed_network_bound n and p ^ (1 / (n : ℝ)) + q ^ (1 / (n : ℝ)) ≤ open_network_bound n.
-/

/-- Parity effect and tight quantum bounds for n-source networks (Theorem 4). -/
theorem parity_effect_quantum_network_bounds
    (n : ℕ) (hn : 1 ≤ n) (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hp1 : p ≤ 1) (hq1 : q ≤ 1)
    (h_odd : ¬ Even n → p ^ 2 + q ^ 2 ≤ 1) :
    Real.sqrt (p ^ (2 / (n : ℝ)) + q ^ (2 / (n : ℝ))) ≤ closed_network_bound n ∧
    p ^ (1 / (n : ℝ)) + q ^ (1 / (n : ℝ)) ≤ open_network_bound n := by
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  rcases Nat.even_or_odd n with hev | hod
  · have hcl : closed_network_bound n = Real.sqrt 2 := by
      simp only [closed_network_bound]
      rw [if_pos hev]
    have hop : open_network_bound n = 2 := by
      simp only [open_network_bound]
      rw [if_pos hev]
    constructor
    · rw [hcl]
      apply Real.sqrt_le_sqrt
      have h1 : p ^ (2/(n:ℝ)) ≤ 1 := Real.rpow_le_one hp hp1 (by positivity)
      have h2 : q ^ (2/(n:ℝ)) ≤ 1 := Real.rpow_le_one hq hq1 (by positivity)
      linarith
    · rw [hop]
      have h1 : p ^ (1/(n:ℝ)) ≤ 1 := Real.rpow_le_one hp hp1 (by positivity)
      have h2 : q ^ (1/(n:ℝ)) ≤ 1 := Real.rpow_le_one hq hq1 (by positivity)
      linarith
  · rcases eq_or_lt_of_le hn with h1 | h2
    · have hn1 : n = 1 := h1.symm
      subst hn1
      have h1odd : ¬ Even 1 := by rintro ⟨k, hk⟩; omega
      have hpq : p^2 + q^2 ≤ 1 := h_odd h1odd
      have hcl1 : closed_network_bound 1 = 1 := by
        simp only [closed_network_bound]
        rw [if_neg h1odd]
        norm_num
      have hop1 : open_network_bound 1 = Real.sqrt 2 := by
        simp only [open_network_bound]
        rw [if_neg h1odd, Real.sqrt_eq_rpow]
        norm_num
      constructor
      · rw [hcl1]
        have hp2 : p ^ (2 / ((1:ℕ):ℝ)) = p^2 := by rw [Nat.cast_one, div_one, Real.rpow_two]
        have hq2 : q ^ (2 / ((1:ℕ):ℝ)) = q^2 := by rw [Nat.cast_one, div_one, Real.rpow_two]
        rw [hp2, hq2, Real.sqrt_le_one]
        exact hpq
      · rw [hop1]
        have hp1' : p ^ (1 / ((1:ℕ):ℝ)) = p := by rw [Nat.cast_one, div_one, Real.rpow_one]
        have hq1' : q ^ (1 / ((1:ℕ):ℝ)) = q := by rw [Nat.cast_one, div_one, Real.rpow_one]
        rw [hp1', hq1']
        have hsq : (p+q)^2 ≤ 2 := by nlinarith [sq_nonneg (p - q)]
        rw [Real.le_sqrt (by positivity) (by norm_num)]
        exact hsq
    · have hn2 : 2 ≤ n := by omega
      have hne : ¬ Even n := Nat.not_even_iff_odd.mpr hod
      have hpq : p^2 + q^2 ≤ 1 := h_odd hne
      have hn0 : (n:ℝ) ≠ 0 := by positivity
      have hcl : closed_network_bound n = (2:ℝ)^(1/2 - 1/(2*(n:ℝ))) := by
        simp only [closed_network_bound]
        rw [if_neg hne]
      have hop : open_network_bound n = (2:ℝ)^(1 - 1/(2*(n:ℝ))) := by
        simp only [open_network_bound]
        rw [if_neg hne]
      have hr1pos : 0 < 2/(n:ℝ) := by positivity
      have hr1le : 2/(n:ℝ) ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact_mod_cast hn2
      have hconc1 := concave_power_sum_le p q (2/(n:ℝ)) hp hq hpq hr1pos hr1le
      have hkey : (1:ℝ) - (2/(n:ℝ))/2 = 1 - 1/(n:ℝ) := by
        field_simp
      have hsum : p ^ (2/(n:ℝ)) + q ^ (2/(n:ℝ)) ≤ (2:ℝ)^(1 - 1/(n:ℝ)) := by
        rw [hkey] at hconc1
        exact hconc1
      have hr2pos : 0 < 1/(n:ℝ) := by positivity
      have hr2le : 1/(n:ℝ) ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact_mod_cast (show 1 ≤ n by omega)
      constructor
      · rw [hcl]
        calc Real.sqrt (p^(2/(n:ℝ))+q^(2/(n:ℝ))) ≤ Real.sqrt ((2:ℝ)^(1-1/(n:ℝ))) := Real.sqrt_le_sqrt hsum
          _ = (2:ℝ)^(1/2 - 1/(2*(n:ℝ))) := by
              rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
              congr 1
              field_simp
      · rw [hop]
        calc p^(1/(n:ℝ))+q^(1/(n:ℝ)) ≤ (2:ℝ)^(1 - (1/(n:ℝ))/2) :=
              concave_power_sum_le p q (1/(n:ℝ)) hp hq hpq hr2pos hr2le
          _ = (2:ℝ)^(1 - 1/(2*(n:ℝ))) := by
              congr 1
              field_simp
