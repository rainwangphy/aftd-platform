import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.NumberTheory.PostageStampNumberNegTwoOfOddNotCoprime
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.NumberTheory.PostageStampNumberNegTwoOfOddDvdEq

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
  have hUL : (y-1)*(1-x) - (((m^2+4*m : ℕ) : ℤ) - (2*(m:ℤ)+2)*y + 1 + (y-1)*(y-x)) =
      2 - (y - ((m:ℤ)+2))^2 := by push_cast; ring
  have hsq : (y - ((m:ℤ)+2))^2 ≤ 2 := by linarith
  have hy3 : y - ((m:ℤ)+2) ≤ 1 ∧ -1 ≤ y - ((m:ℤ)+2) := by
    constructor <;> nlinarith [sq_nonneg (y - ((m:ℤ)+2) - 1), sq_nonneg (y - ((m:ℤ)+2) + 1)]
  have hmZ : (5:ℤ) ≤ (m:ℤ) := by exact_mod_cast hm
  have hpos : (0:ℤ) < 2*(m:ℤ)+1 := by positivity
  have hneg : (2*(m:ℤ)+1)*a < 0 := mul_neg_of_pos_of_neg hpos ha
  have ha1 : (2*(m:ℤ)+1)*a ≤ -(2*(m:ℤ)+1) := by
    nlinarith [mul_le_mul_of_nonneg_left (show a ≤ -1 by omega) hpos.le]
  have hm3 : (m:ℤ) % 3 = 2 := by omega
  rcases (show y = (m:ℤ)+1 ∨ y = (m:ℤ)+2 ∨ y = (m:ℤ)+3 by omega) with hy | hy | hy
  · subst hy
    have hb : (m:ℤ)*(1-x) - 1 ≤ (2*(m:ℤ)+1)*a := by nlinarith
    have hU : (2*(m:ℤ)+1)*a ≤ (m:ℤ)*(1-x) := by nlinarith
    have hxm : x ≤ (m:ℤ) := by linarith
    rcases (show (2*(m:ℤ)+1)*a = (m:ℤ)*(1-x) - 0 ∨ (2*(m:ℤ)+1)*a = (m:ℤ)*(1-x) - 1 by omega)
      with he | he
    · have hd : (2*(m:ℤ)+1) ∣ x - 1 - 2*0 := ⟨2*a - 1 + x, by linear_combination (-2) * he⟩
      have h0 := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> linarith)
      have : x = 1 := by linarith
      subst this; nlinarith
    · have hd : (2*(m:ℤ)+1) ∣ x - 1 - 2*1 := ⟨2*a - 1 + x, by linear_combination (-2) * he⟩
      have h0 := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> linarith)
      exact postage_stamp_number_neg_two_of_odd_not_coprime x ((m:ℤ)+1) 3 (by norm_num)
        ⟨1, by linarith⟩ ⟨((m:ℤ)+1)/3, by omega⟩ hcop
  · subst hy
    have hb : ((m:ℤ)+1)*(1-x) - 2 ≤ (2*(m:ℤ)+1)*a := by nlinarith
    have hU : (2*(m:ℤ)+1)*a ≤ ((m:ℤ)+1)*(1-x) := by nlinarith
    have hxm : x ≤ (m:ℤ)+1 := by linarith
    rcases (show (2*(m:ℤ)+1)*a = ((m:ℤ)+1)*(1-x) - 0 ∨ (2*(m:ℤ)+1)*a = ((m:ℤ)+1)*(1-x) - 1 ∨
        (2*(m:ℤ)+1)*a = ((m:ℤ)+1)*(1-x) - 2 by omega) with he | he | he
    · have hd : (2*(m:ℤ)+1) ∣ x + 2*0 - 1 := ⟨1 - x - 2*a, by linear_combination 2 * he⟩
      have h0 := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> linarith)
      have : x = 1 := by linarith
      subst this; nlinarith
    · have hd : (2*(m:ℤ)+1) ∣ x + 2*1 - 1 := ⟨1 - x - 2*a, by linear_combination 2 * he⟩
      have h0 := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> linarith)
      linarith
    · have hd : (2*(m:ℤ)+1) ∣ x + 2*2 - 1 := ⟨1 - x - 2*a, by linear_combination 2 * he⟩
      have h0 := Int.eq_zero_of_abs_lt_dvd hd (by rw [abs_lt]; constructor <;> linarith)
      linarith
  · subst hy
    have hb : ((m:ℤ)+2)*(1-x) - 1 ≤ (2*(m:ℤ)+1)*a := by nlinarith
    have hU : (2*(m:ℤ)+1)*a ≤ ((m:ℤ)+2)*(1-x) := by nlinarith
    have hxm : x ≤ (m:ℤ)+2 := by linarith
    have hx2 : 2 ≤ x := by
      by_contra hc
      have : x = 1 := by omega
      subst this; nlinarith
    rcases (show (2*(m:ℤ)+1)*a = ((m:ℤ)+2)*(1-x) - 0 ∨
        (2*(m:ℤ)+1)*a = ((m:ℤ)+2)*(1-x) - 1 by omega) with he | he
    · have hd : (2*(m:ℤ)+1) ∣ 3*(x-1) + 2*0 := ⟨1 - x - 2*a, by linear_combination 2 * he⟩
      have h1 := postage_stamp_number_neg_two_of_odd_dvd_eq _ _ hpos hd (by linarith) (by linarith)
      omega
    · have hd : (2*(m:ℤ)+1) ∣ 3*(x-1) + 2*1 := ⟨1 - x - 2*a, by linear_combination 2 * he⟩
      have h1 := postage_stamp_number_neg_two_of_odd_dvd_eq _ _ hpos hd (by linarith) (by linarith)
      obtain ⟨r, hr⟩ : ∃ r : ℕ, m = 6*r+5 := ⟨m/6, by omega⟩
      have hxr : x = 4*(r:ℤ)+4 := by rw [hr] at h1; push_cast at h1; omega
      exact postage_stamp_number_neg_two_of_odd_not_coprime x ((m:ℤ)+3) 2 (by norm_num)
        ⟨2*(r:ℤ)+2, by rw [hxr]; ring⟩ ⟨3*(r:ℤ)+4, by rw [hr]; push_cast; ring⟩ hcop
