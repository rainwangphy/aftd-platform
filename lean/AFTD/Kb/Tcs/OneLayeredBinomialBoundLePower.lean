import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# one_layered_binomial_bound_le_power

Topic: combinatorics   Node: ad31c17bb64a

Provenance: formalization of a published result. Source: arXiv:2611.08071 Theorem 2.1

For integers r ≥ 1 and m ≥ r, the binomial bound (m - r + 1) * choose(⌊log_2(m - r + 1)⌋ + r - 1, r - 1) is at most (m - r + 1)^(1 + log_2 r) over the real numbers.
-/

lemma one_layered_binomial_bound_le_power_choose_add_le_pow (L r : ℕ) (hr : 1 ≤ r) :
    (L + r - 1).choose L ≤ r ^ L := by
  induction' L with L ih
  · simp
  · have h1 : (L + r) * (L + r - 1).choose L = (L + r).choose (L + 1) * (L + 1) := by
      have h2 := Nat.add_one_mul_choose_eq (L + r - 1) L
      have h3 : L + r - 1 + 1 = L + r := Nat.sub_add_cancel (by omega)
      rwa [h3] at h2
    have h4 : (L + r).choose (L + 1) * (L + 1) ≤ r ^ (L + 1) * (L + 1) := by
      calc
        (L + r).choose (L + 1) * (L + 1) = (L + r) * (L + r - 1).choose L := h1.symm
        _ ≤ (L + r) * r ^ L := Nat.mul_le_mul_left _ ih
        _ ≤ (r * (L + 1)) * r ^ L := by
          apply Nat.mul_le_mul_right
          nlinarith
        _ = r ^ (L + 1) * (L + 1) := by
          ring
    have hpos : 0 < L + 1 := by omega
    have h5 : (L + 1 + r - 1) = L + r := by omega
    rw [h5]
    exact Nat.le_of_mul_le_mul_right h4 hpos

lemma one_layered_binomial_bound_le_power_choose_symm (L r : ℕ) (hr : 1 ≤ r) :
    (L + r - 1).choose (r - 1) = (L + r - 1).choose L := by
  have hle : r - 1 ≤ L + r - 1 := by omega
  have heq : L + r - 1 - (r - 1) = L := by omega
  have := Nat.choose_symm hle
  rw [heq] at this
  exact this.symm

lemma one_layered_binomial_bound_le_power_two_rpow_log_div_log (r : ℕ) (hr : 1 ≤ r) :
    (2 : ℝ) ^ (Real.log (r : ℝ) / Real.log 2) = (r : ℝ) := by
  have h2pos : (0 : ℝ) < 2 := by norm_num
  have hrpos : (0 : ℝ) < (r : ℝ) := by positivity
  rw [Real.rpow_def_of_pos h2pos]
  have hlog2 : Real.log 2 ≠ 0 := by
    apply Real.log_ne_zero_of_pos_of_ne_one <;> norm_num
  have : Real.log 2 * (Real.log (r : ℝ) / Real.log 2) = Real.log (r : ℝ) := by
    exact mul_div_cancel₀ (Real.log (r : ℝ)) hlog2
  rw [this, Real.exp_log hrpos]

/-- The bound κ_r(m) ≤ (m - r + 1)^(1 + log_2 r). -/
theorem one_layered_binomial_bound_le_power (m r : ℕ) (hr : 1 ≤ r) (hm : r ≤ m) :
    ((m - r + 1 : ℝ) * ((Nat.log 2 (m - r + 1) + r - 1).choose (r - 1) : ℝ)) ≤
      (m - r + 1 : ℝ) ^ (1 + Real.log (r : ℝ) / Real.log 2) := by
  have hk_cast : (m - r + 1 : ℝ) = ((m - r + 1 : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub hm]; rfl
  rw [hk_cast]
  set k := m - r + 1
  set L := Nat.log 2 k
  have hk : 1 ≤ k := by omega
  have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
  have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by positivity
  have hc_nonneg : 0 ≤ Real.log (r : ℝ) / Real.log 2 := by
    have hr' : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have h1 : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg hr'
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    exact div_nonneg h1 (le_of_lt h2)
  have hchoose : ((L + r - 1).choose (r - 1) : ℝ) ≤ (r : ℝ) ^ L := by
    rw [one_layered_binomial_bound_le_power_choose_symm L r hr]
    have := one_layered_binomial_bound_le_power_choose_add_le_pow L r hr
    exact_mod_cast this
  have hpow_le : (r : ℝ) ^ L ≤ (k : ℝ) ^ (Real.log (r : ℝ) / Real.log 2) := by
    have h2 : (0 : ℝ) ≤ 2 := by norm_num
    have h_r_L : (r : ℝ) ^ L = ((2 ^ L : ℕ) : ℝ) ^ (Real.log (r : ℝ) / Real.log 2) := by
      push_cast
      rw [← Real.rpow_natCast_mul h2, mul_comm, Real.rpow_mul_natCast h2]
      rw [one_layered_binomial_bound_le_power_two_rpow_log_div_log r hr]
    rw [h_r_L]
    have h2L_le_k : 2 ^ L ≤ k := by
      apply Nat.pow_log_le_self
      omega
    have h2L_le_k_real : ((2 ^ L : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast h2L_le_k
    have h2L_nonneg : (0 : ℝ) ≤ ((2 ^ L : ℕ) : ℝ) := by positivity
    exact Real.rpow_le_rpow h2L_nonneg h2L_le_k_real hc_nonneg
  calc
    (k : ℝ) * ((L + r - 1).choose (r - 1) : ℝ)
      ≤ (k : ℝ) * ((r : ℝ) ^ L) := by gcongr
    _ ≤ (k : ℝ) * ((k : ℝ) ^ (Real.log (r : ℝ) / Real.log 2)) := by gcongr
    _ = (k : ℝ) ^ (1 + Real.log (r : ℝ) / Real.log 2) := by
      rw [Real.rpow_add hk_pos, Real.rpow_one]
