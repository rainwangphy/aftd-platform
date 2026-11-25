import AFTD.Prelude
import AFTD.Kb.Tcs.ConsecutiveSumBoundK
import AFTD.Kb.Tcs.ConsecutiveSumAp
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# consecutive_sum_ap_distinct_sums

Topic: combinatorics   Node: 9eb07374c568

Provenance: helper lemma. arXiv:2611.30462 Theorem 3.2

For integers a and K with 1 ≤ a, 1 ≤ K, and K ≤ a, and natural numbers u, r, v, s such that u + r ≤ consecutive_sum_bound_k a K, 0 < r, v + s ≤ consecutive_sum_bound_k a K, and 0 < s, if ∑ i ∈ Finset.Ioc u (u + r), consecutive_sum_ap a K i = ∑ j ∈ Finset.Ioc v (v + s), consecutive_sum_ap a K j, then u = v and r = s.
-/

open Finset

lemma consecutive_sum_ap_distinct_sums_two_mul_sum_Ioc_id (u r : ℕ) :
    2 * ∑ i ∈ Ioc u (u + r), (i : ℤ) = (r : ℤ) * (2 * (u : ℤ) + (r : ℤ) + 1) := by
  induction r with
  | zero => simp
  | succ r' ih =>
    have hle : u ≤ u + r' := Nat.le_add_right u r'
    rw [← add_assoc, sum_Ioc_succ_top hle]
    push_cast
    linarith

lemma consecutive_sum_ap_distinct_sums_sum_ap (a K : ℤ) (u r : ℕ) :
    ∑ i ∈ Ioc u (u + r), consecutive_sum_ap a K i =
    (r : ℤ) * (a - K) + K * ∑ i ∈ Ioc u (u + r), (i : ℤ) := by
  have : ∀ i ∈ Ioc u (u + r), consecutive_sum_ap a K i = (a - K) + (i : ℤ) * K := by
    intro i _
    dsimp [consecutive_sum_ap]
    ring
  rw [sum_congr rfl this]
  rw [sum_add_distrib, sum_const, nsmul_eq_mul, Nat.card_Ioc, Nat.add_sub_cancel_left]
  have h_comm : ∑ x ∈ Ioc u (u + r), (x : ℤ) * K = K * ∑ i ∈ Ioc u (u + r), (i : ℤ) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro x _
    ring
  rw [h_comm]

lemma consecutive_sum_ap_distinct_sums_two_mul_sum_ap (a K : ℤ) (u r : ℕ) :
    2 * ∑ i ∈ Ioc u (u + r), consecutive_sum_ap a K i =
    2 * (r : ℤ) * (a - K) + K * (r : ℤ) * (2 * (u : ℤ) + (r : ℤ) + 1) := by
  have h1 := consecutive_sum_ap_distinct_sums_sum_ap a K u r
  have h2 := consecutive_sum_ap_distinct_sums_two_mul_sum_Ioc_id u r
  calc 2 * ∑ i ∈ Ioc u (u + r), consecutive_sum_ap a K i
    _ = 2 * ((r : ℤ) * (a - K) + K * ∑ i ∈ Ioc u (u + r), (i : ℤ)) := by rw [h1]
    _ = 2 * (r : ℤ) * (a - K) + K * (2 * ∑ i ∈ Ioc u (u + r), (i : ℤ)) := by ring
    _ = 2 * (r : ℤ) * (a - K) + K * (r : ℤ) * (2 * (u : ℤ) + (r : ℤ) + 1) := by rw [h2]; ring

lemma consecutive_sum_ap_distinct_sums_k_sq_mul_le (a K : ℤ) (hK : 1 ≤ K) (haK : K ≤ a) :
    K * ((consecutive_sum_bound_k a K : ℤ))^2 ≤ 4 * (a - K) := by
  have hKa_real : (K : ℝ) ≤ a := by exact_mod_cast haK
  have hKpos : (0 : ℝ) < (K : ℝ) := by positivity
  have h_nonneg : 0 ≤ (a : ℝ) / (K : ℝ) - 1 := by
    rw [sub_nonneg]
    rw [le_div_iff₀ hKpos]
    linarith
  have h_sqrt_nonneg : 0 ≤ 2 * Real.sqrt ((a : ℝ) / (K : ℝ) - 1) := by positivity
  have h_floor := Nat.floor_le h_sqrt_nonneg
  have h1 : (consecutive_sum_bound_k a K : ℝ) ^ 2 ≤
      (2 * Real.sqrt ((a : ℝ) / (K : ℝ) - 1)) ^ 2 := by
    dsimp [consecutive_sum_bound_k]
    nlinarith
  have h2 : (2 * Real.sqrt ((a : ℝ) / (K : ℝ) - 1)) ^ 2 = 4 * ((a : ℝ) / (K : ℝ) - 1) := by
    calc (2 * Real.sqrt ((a : ℝ) / (K : ℝ) - 1)) ^ 2
      _ = 4 * (Real.sqrt ((a : ℝ) / (K : ℝ) - 1)) ^ 2 := by ring
      _ = 4 * ((a : ℝ) / (K : ℝ) - 1) := by rw [Real.sq_sqrt h_nonneg]
  have h_real : (K : ℝ) * (consecutive_sum_bound_k a K : ℝ)^2 ≤ 4 * ((a : ℝ) - (K : ℝ)) := by
    have h_div : 4 * ((a : ℝ) / (K : ℝ) - 1) * (K : ℝ) = 4 * ((a : ℝ) - (K : ℝ)) := by
      calc 4 * ((a : ℝ) / (K : ℝ) - 1) * (K : ℝ)
        _ = 4 * (((a : ℝ) / (K : ℝ)) * (K : ℝ) - (K : ℝ)) := by ring
        _ = 4 * ((a : ℝ) - (K : ℝ)) := by rw [div_mul_cancel₀ _ (ne_of_gt hKpos)]
    nlinarith
  exact_mod_cast h_real

lemma consecutive_sum_ap_distinct_sums_not_lt (a K : ℤ) (hK : 1 ≤ K) (haK : K ≤ a)
    (u r v s : ℕ)
    (hur : u + r ≤ consecutive_sum_bound_k a K) (hr : 0 < r)
    (hrs : r < s)
    (hsum : ∑ i ∈ Finset.Ioc u (u + r), consecutive_sum_ap a K i =
            ∑ j ∈ Finset.Ioc v (v + s), consecutive_sum_ap a K j) :
    False := by
  let k : ℤ := (consecutive_sum_bound_k a K : ℤ)
  have hrs_int : (r : ℤ) + 1 ≤ (s : ℤ) := by exact_mod_cast hrs
  have hr_ge : 1 ≤ (r : ℤ) := by exact_mod_cast hr
  have hu_le : (u : ℤ) + (r : ℤ) ≤ k := by
    show (u : ℤ) + (r : ℤ) ≤ (consecutive_sum_bound_k a K : ℤ)
    exact_mod_cast hur
  have hv_ge : 0 ≤ (v : ℤ) := by exact_mod_cast (Nat.zero_le v)
  have hsum2 : 2 * ∑ i ∈ Finset.Ioc u (u + r), consecutive_sum_ap a K i =
      2 * ∑ j ∈ Finset.Ioc v (v + s), consecutive_sum_ap a K j := by rw [hsum]
  rw [consecutive_sum_ap_distinct_sums_two_mul_sum_ap, consecutive_sum_ap_distinct_sums_two_mul_sum_ap] at hsum2
  have hsum_eq : 2 * ((s : ℤ) - (r : ℤ)) * (a - K) =
      K * ((r : ℤ) * (2 * (u : ℤ) + (r : ℤ) + 1) - (s : ℤ) * (2 * (v : ℤ) + (s : ℤ) + 1)) := by
    linarith [hsum2]
  have hk_bound : K * k^2 ≤ 4 * (a - K) := consecutive_sum_ap_distinct_sums_k_sq_mul_le a K hK haK
  have hk_le : k^2 ≤ 2 * ((r : ℤ) * (2 * (u : ℤ) + (r : ℤ) + 1) - (s : ℤ) * (2 * (v : ℤ) + (s : ℤ) + 1)) := by
    have h1 : 4 * (a - K) ≤ 4 * ((s : ℤ) - (r : ℤ)) * (a - K) := by
      have : 1 ≤ (s : ℤ) - (r : ℤ) := by linarith
      have : 0 ≤ a - K := by linarith
      nlinarith
    have h2 : K * k^2 ≤ K * (2 * ((r : ℤ) * (2 * (u : ℤ) + (r : ℤ) + 1) - (s : ℤ) * (2 * (v : ℤ) + (s : ℤ) + 1))) := by
      linarith [hk_bound, h1, hsum_eq]
    have hK_pos : 0 < K := by linarith
    exact le_of_mul_le_mul_left h2 hK_pos
  have h_ub : 2 * ((r : ℤ) * (2 * (u : ℤ) + (r : ℤ) + 1) - (s : ℤ) * (2 * (v : ℤ) + (s : ℤ) + 1)) ≤
      4 * (r : ℤ) * (k - (r : ℤ) - 1) - 4 := by
    have h_r_term : (r : ℤ) * (2 * (u : ℤ) + (r : ℤ) + 1) ≤ (r : ℤ) * (2 * k - (r : ℤ) + 1) := by
      have : 2 * (u : ℤ) + (r : ℤ) + 1 ≤ 2 * k - (r : ℤ) + 1 := by linarith
      nlinarith
    have h_s_term : ((r : ℤ) + 1) * ((r : ℤ) + 2) ≤ (s : ℤ) * (2 * (v : ℤ) + (s : ℤ) + 1) := by
      have : (r : ℤ) + 2 ≤ 2 * (v : ℤ) + (s : ℤ) + 1 := by linarith
      nlinarith
    linarith
  have h_quad : 4 * (r : ℤ) * (k - (r : ℤ) - 1) - 4 < k^2 := by
    have hsq : 0 ≤ (k - 2 * (r : ℤ))^2 := sq_nonneg _
    have h_id : 4 * (r : ℤ) * (k - (r : ℤ) - 1) - 4 - k^2 = -((k - 2 * (r : ℤ))^2 + 4 * (r : ℤ) + 4) := by ring
    linarith
  linarith

/-- Consecutive sums in the arithmetic progression of length k = ⌊2√(a/K - 1)⌋ are distinct. -/
theorem consecutive_sum_ap_distinct_sums (a K : ℤ) (ha : 1 ≤ a) (hK : 1 ≤ K) (haK : K ≤ a)
    (u r v s : ℕ)
    (hur : u + r ≤ consecutive_sum_bound_k a K) (hr : 0 < r)
    (hvs : v + s ≤ consecutive_sum_bound_k a K) (hs : 0 < s)
    (hsum : ∑ i ∈ Finset.Ioc u (u + r), consecutive_sum_ap a K i =
            ∑ j ∈ Finset.Ioc v (v + s), consecutive_sum_ap a K j) :
    u = v ∧ r = s := by
  have h_not_lt : ¬ (r < s) := fun hlt =>
    consecutive_sum_ap_distinct_sums_not_lt a K hK haK u r v s hur hr hlt hsum
  have h_not_gt : ¬ (s < r) := fun hgt =>
    consecutive_sum_ap_distinct_sums_not_lt a K hK haK v s u r hvs hs hgt hsum.symm
  have hrs : r = s := by omega
  subst hrs
  have hsum2 : 2 * ∑ i ∈ Finset.Ioc u (u + r), consecutive_sum_ap a K i =
      2 * ∑ j ∈ Finset.Ioc v (v + r), consecutive_sum_ap a K j := by rw [hsum]
  rw [consecutive_sum_ap_distinct_sums_two_mul_sum_ap, consecutive_sum_ap_distinct_sums_two_mul_sum_ap] at hsum2
  have huv_diff : 2 * K * (r : ℤ) * ((u : ℤ) - (v : ℤ)) = 0 := by linarith [hsum2]
  have hKr_pos : 0 < 2 * K * (r : ℤ) := by
    have : (0 : ℤ) < (r : ℤ) := by exact_mod_cast hr
    nlinarith
  have h_sub : (u : ℤ) - (v : ℤ) = 0 := by nlinarith [huv_diff, hKr_pos]
  have huv : u = v := Nat.cast_inj.mp (sub_eq_zero.mp h_sub)
  exact ⟨huv, rfl⟩
