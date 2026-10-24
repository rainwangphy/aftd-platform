import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# postage_stamp_number_neg_two_of_odd_cases_two

Topic: elementary_number_theory   Node: 5f933974277d

Provenance: helper lemma. arXiv:2610.19470 (Positivity and negativity for h-bases for N), Theorem 4.1 and its proof

For h = 2m+1 with m ≡ 5 (mod 6), m ≥ 5: no coprime x < y and a < 0 satisfy the Theorem 4.1 inequalities at range m² + 4m = n_h(2) - 2.
-/

theorem postage_stamp_number_neg_two_of_odd_cases_two
    (m : ℕ) (hm : 5 ≤ m) (hm6 : m % 6 = 5) (a x y : ℤ) (hx : 0 < x) (hxy : x < y) (ha : a < 0)
    (hcop : IsCoprime x y) (haU : (2*(m:ℤ)+1)*a ≤ (y-1)*(1-x))
    (haL : ((m^2+4*m : ℕ) : ℤ) - (2*(m:ℤ)+2)*y + 1 + (y-1)*(y-x) ≤ (2*(m:ℤ)+1)*a) : False := by
  have hdiff : (y - 1) * (1 - x) - (((m^2+4*m : ℕ) : ℤ) - (2*(m:ℤ)+2)*y + 1 + (y-1)*(y-x)) =
      2 - (y - ((m:ℤ) + 2))^2 := by
    push_cast
    ring
  have hsq_le : (y - ((m:ℤ) + 2))^2 ≤ 2 := by
    linarith
  have hd_cases : y - ((m:ℤ) + 2) = -1 ∨ y - ((m:ℤ) + 2) = 0 ∨ y - ((m:ℤ) + 2) = 1 := by
    have h1 : y - ((m:ℤ) + 2) < 2 := by
      by_contra!
      have : 4 ≤ (y - ((m:ℤ) + 2))^2 := by nlinarith
      linarith
    have h2 : -2 < y - ((m:ℤ) + 2) := by
      by_contra!
      have : 4 ≤ (y - ((m:ℤ) + 2))^2 := by nlinarith
      linarith
    omega
  let k := (y - 1) * (1 - x) - (2*(m:ℤ)+1)*a
  have hk_def : (2*(m:ℤ)+1)*a = (y - 1) * (1 - x) - k := by ring
  have hk_nonneg : 0 ≤ k := by linarith
  have hk_le : k ≤ 2 - (y - ((m:ℤ) + 2))^2 := by linarith
  rcases hd_cases with hd | hd | hd
  · -- y - (m + 2) = -1, so y = m + 1
    have hy : y = (m:ℤ) + 1 := by omega
    have hk1 : k ≤ 1 := by
      have : (y - ((m:ℤ) + 2))^2 = 1 := by rw [hd]; ring
      linarith
    rw [hy] at hk_def hxy
    have heq : (2*(m:ℤ)+1)*a = (m:ℤ)*(1 - x) - k := by
      calc (2*(m:ℤ)+1)*a = ((m:ℤ)+1 - 1)*(1 - x) - k := hk_def
      _ = (m:ℤ)*(1 - x) - k := by ring
    have hC_eq : (m:ℤ) * (2*a + x - 1) = -a - k := by
      calc (m:ℤ) * (2*a + x - 1) = 2*(m:ℤ)*a + (m:ℤ)*x - (m:ℤ) := by ring
      _ = (2*(m:ℤ)+1)*a - a + (m:ℤ)*x - (m:ℤ) := by ring
      _ = ((m:ℤ)*(1 - x) - k) - a + (m:ℤ)*x - (m:ℤ) := by rw [heq]
      _ = -a - k := by ring
    have hC_nonneg : 0 ≤ 2*a + x - 1 := by
      have : 0 ≤ -a - k := by omega
      have : (0 : ℤ) < (m:ℤ) := by omega
      nlinarith
    have hC_not_pos : ¬ (1 ≤ 2*a + x - 1) := by
      intro hC1
      have h1 : (m:ℤ) ≤ -a - k := by
        calc (m:ℤ) = (m:ℤ) * 1 := by ring
        _ ≤ (m:ℤ) * (2*a + x - 1) := by nlinarith [show (0 : ℤ) < (m:ℤ) by omega]
        _ = -a - k := hC_eq
      omega
    have hC0 : 2*a + x - 1 = 0 := by omega
    have h_rhs0 : -a - k = 0 := by
      calc -a - k = (m:ℤ) * (2*a + x - 1) := hC_eq.symm
      _ = (m:ℤ) * 0 := by rw [hC0]
      _ = 0 := by ring
    have hx3 : x = 3 := by omega
    have hdvd3y : (3 : ℤ) ∣ y := by
      omega
    have hdvd3x : (3 : ℤ) ∣ x := by
      rw [hx3]
    have hunit : IsUnit (3 : ℤ) := hcop.isUnit_of_dvd' hdvd3x hdvd3y
    rw [Int.isUnit_iff] at hunit
    omega
  · -- y - (m + 2) = 0, so y = m + 2
    have hy : y = (m:ℤ) + 2 := by omega
    have hk2 : k ≤ 2 := by
      have : (y - ((m:ℤ) + 2))^2 = 0 := by rw [hd]; ring
      linarith
    rw [hy] at hk_def hxy
    have heq : (2*(m:ℤ)+1)*a = ((m:ℤ)+1)*(1 - x) - k := by
      calc (2*(m:ℤ)+1)*a = ((m:ℤ)+2 - 1)*(1 - x) - k := hk_def
      _ = ((m:ℤ)+1)*(1 - x) - k := by ring
    have hC_eq : (2*(m:ℤ) + 1) * (2*a + x - 1) = 1 - x - 2*k := by
      calc (2*(m:ℤ) + 1) * (2*a + x - 1) = 2 * ((2*(m:ℤ)+1)*a) + (2*(m:ℤ)+1)*(x - 1) := by ring
      _ = 2 * (((m:ℤ)+1)*(1 - x) - k) + (2*(m:ℤ)+1)*(x - 1) := by rw [heq]
      _ = 1 - x - 2*k := by ring
    have hC_le_zero : 2*a + x - 1 ≤ 0 := by
      have : 1 - x - 2*k ≤ 0 := by omega
      have : 0 < 2*(m:ℤ) + 1 := by omega
      nlinarith
    have hC_not_neg : ¬ (2*a + x - 1 ≤ -1) := by
      intro hC1
      have h1 : 1 - x - 2*k ≤ -(2*(m:ℤ) + 1) := by
        calc 1 - x - 2*k = (2*(m:ℤ) + 1) * (2*a + x - 1) := hC_eq.symm
        _ ≤ (2*(m:ℤ) + 1) * (-1) := by nlinarith [show 0 < 2*(m:ℤ) + 1 by omega]
        _ = -(2*(m:ℤ) + 1) := by ring
      omega
    have hC0 : 2*a + x - 1 = 0 := by omega
    have h_rhs0 : 1 - x - 2*k = 0 := by
      calc 1 - x - 2*k = (2*(m:ℤ) + 1) * (2*a + x - 1) := hC_eq.symm
      _ = (2*(m:ℤ) + 1) * 0 := by rw [hC0]
      _ = 0 := by ring
    omega
  · -- y - (m + 2) = 1, so y = m + 3
    have hy : y = (m:ℤ) + 3 := by omega
    have hk1 : k ≤ 1 := by
      have : (y - ((m:ℤ) + 2))^2 = 1 := by rw [hd]; ring
      linarith
    rw [hy] at hk_def hxy
    have heq : (2*(m:ℤ)+1)*a = ((m:ℤ)+2)*(1 - x) - k := by
      calc (2*(m:ℤ)+1)*a = ((m:ℤ)+3 - 1)*(1 - x) - k := hk_def
      _ = ((m:ℤ)+2)*(1 - x) - k := by ring
    have hC_eq : (2*(m:ℤ) + 1) * (2*a + x - 1) = 3*(1 - x) - 2*k := by
      calc (2*(m:ℤ) + 1) * (2*a + x - 1) = 2 * ((2*(m:ℤ)+1)*a) + (2*(m:ℤ)+1)*(x - 1) := by ring
      _ = 2 * (((m:ℤ)+2)*(1 - x) - k) + (2*(m:ℤ)+1)*(x - 1) := by rw [heq]
      _ = 3*(1 - x) - 2*k := by ring
    have hC_le_zero : 2*a + x - 1 ≤ 0 := by
      have : 3*(1 - x) - 2*k ≤ 0 := by omega
      have : 0 < 2*(m:ℤ) + 1 := by omega
      nlinarith
    have hC_not_le_neg_two : ¬ (2*a + x - 1 ≤ -2) := by
      intro hC2
      have h1 : 3*(1 - x) - 2*k ≤ -2 * (2*(m:ℤ) + 1) := by
        calc 3*(1 - x) - 2*k = (2*(m:ℤ) + 1) * (2*a + x - 1) := hC_eq.symm
        _ ≤ (2*(m:ℤ) + 1) * (-2) := by nlinarith [show 0 < 2*(m:ℤ) + 1 by omega]
        _ = -2 * (2*(m:ℤ) + 1) := by ring
      omega
    have hC_cases : 2*a + x - 1 = 0 ∨ 2*a + x - 1 = -1 := by omega
    rcases hC_cases with hC0 | hC1
    · have h_rhs0 : 3*(1 - x) - 2*k = 0 := by
        calc 3*(1 - x) - 2*k = (2*(m:ℤ) + 1) * (2*a + x - 1) := hC_eq.symm
        _ = (2*(m:ℤ) + 1) * 0 := by rw [hC0]
        _ = 0 := by ring
      omega
    · have h_rhs1 : 3*(1 - x) - 2*k = -(2*(m:ℤ) + 1) := by
        calc 3*(1 - x) - 2*k = (2*(m:ℤ) + 1) * (2*a + x - 1) := hC_eq.symm
        _ = (2*(m:ℤ) + 1) * (-1) := by rw [hC1]
        _ = -(2*(m:ℤ) + 1) := by ring
      have hk_cases : k = 0 ∨ k = 1 := by omega
      rcases hk_cases with hk0 | hk1'
      · have : 3 * x = 2 * (m:ℤ) + 4 := by omega
        omega
      · have : 3 * x = 2 * (m:ℤ) + 2 := by omega
        have hdvd2x : (2 : ℤ) ∣ x := by omega
        have hdvd2y : (2 : ℤ) ∣ y := by omega
        have hunit : IsUnit (2 : ℤ) := hcop.isUnit_of_dvd' hdvd2x hdvd2y
        rw [Int.isUnit_iff] at hunit
        omega
