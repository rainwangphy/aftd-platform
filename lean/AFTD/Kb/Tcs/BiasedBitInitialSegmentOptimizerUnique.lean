import AFTD.Prelude
import AFTD.Kb.Tcs.BiasedBitVulnerability
import AFTD.Kb.Tcs.BiasedBitOptimalVulnerability
import AFTD.Kb.Tcs.TwoPointMask
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.BiasedBitCostVulnerabilityInitialSegment

/-!
# biased_bit_initial_segment_optimizer_unique

Topic: information   Node: f114d26cbd75

Provenance: formalization of a published result. Source: arXiv:2611.16066 Thm 5.5

For any bias parameter p with 1 / 2 < p and p < 1, and any budget c with 0 < c and c ≤ 1 - p, if q is a function from ℤ to ℝ satisfying (∀ s, 0 ≤ q s), HasSum q 1, Summable (fun s : ℤ => |(s : ℝ)| * q s), (∑' s : ℤ, |(s : ℝ)| * q s) ≤ c, and biased_bit_vulnerability p q = biased_bit_optimal_vulnerability p c, then q = two_point_mask c.
-/

/-- On the initial segment (0, 1 - p], any optimal additive integer mask is unique and equals two_point_mask c. -/
theorem biased_bit_initial_segment_optimizer_unique
    (p : ℝ) (hp : 1 / 2 < p) (hp1 : p < 1)
    (c : ℝ) (hc0 : 0 < c) (hc : c ≤ 1 - p)
    (q : ℤ → ℝ) (hq_nonneg : ∀ s, 0 ≤ q s) (hq_sum : HasSum q 1)
    (hq_mom : Summable (fun s : ℤ => |(s : ℝ)| * q s))
    (hq_cost : (∑' s : ℤ, |(s : ℝ)| * q s) ≤ c)
    (hq_opt : biased_bit_vulnerability p q = biased_bit_optimal_vulnerability p c) :
    q = two_point_mask c := by
  have hp0 : 0 < p := by linarith
  have h1p : 0 ≤ 1 - p := by linarith
  have hq : Summable q := hq_sum.summable
  have hqshift : Summable (fun s : ℤ => q (s - 1)) :=
    hq.comp_injective (fun a b hab => by simpa using hab)
  have hqm : Summable (fun s : ℤ => if s ≤ 0 then q s else 0) := by
    apply Summable.of_nonneg_of_le (fun s => ?_) (fun s => ?_) hq
    · split_ifs <;> simp [hq_nonneg]
    · split_ifs with h
      · exact le_rfl
      · exact hq_nonneg s
  have hqpos : Summable (fun s : ℤ => if 0 < s then q s else 0) := by
    apply Summable.of_nonneg_of_le (fun s => ?_) (fun s => ?_) hq
    · split_ifs <;> simp [hq_nonneg]
    · split_ifs with h
      · exact le_rfl
      · exact hq_nonneg s
  have hqneg : Summable (fun s : ℤ => if s < 0 then q s else 0) := by
    apply Summable.of_nonneg_of_le (fun s => ?_) (fun s => ?_) hq
    · split_ifs <;> simp [hq_nonneg]
    · split_ifs with h
      · exact le_rfl
      · exact hq_nonneg s
  have hqge : Summable (fun s : ℤ => if 0 ≤ s then q s else 0) := by
    apply Summable.of_nonneg_of_le (fun s => ?_) (fun s => ?_) hq
    · split_ifs <;> simp [hq_nonneg]
    · split_ifs with h
      · exact le_rfl
      · exact hq_nonneg s
  have hqnz : Summable (fun s : ℤ => if s ≠ 0 then q s else 0) := by
    apply Summable.of_nonneg_of_le (fun s => ?_) (fun s => ?_) hq
    · split_ifs <;> simp [hq_nonneg]
    · split_ifs with h
      · exact le_rfl
      · exact hq_nonneg s
  have hqsh : Summable (fun s : ℤ => if 0 < s then q (s - 1) else 0) := by
    apply Summable.of_nonneg_of_le (fun s => ?_) (fun s => ?_) hqshift
    · split_ifs <;> simp [hq_nonneg]
    · split_ifs with h
      · exact le_rfl
      · exact hq_nonneg (s - 1)
  have hqm_split : (∑' s : ℤ, if s ≤ 0 then q s else 0) = 1 - ∑' s : ℤ, (if 0 < s then q s else 0) := by
    have heq : (fun s : ℤ => (if s ≤ 0 then q s else 0) + (if 0 < s then q s else 0)) = q := by
      funext s
      by_cases h : s ≤ 0
      · simp [h, not_lt.mpr h]
      · simp [h, not_le.mp h]
    have h := hqm.tsum_add hqpos
    rw [heq, hq_sum.tsum_eq] at h
    linarith
  have hqge_split : (∑' s : ℤ, if 0 ≤ s then q s else 0) = 1 - ∑' s : ℤ, (if s < 0 then q s else 0) := by
    have heq : (fun s : ℤ => (if 0 ≤ s then q s else 0) + (if s < 0 then q s else 0)) = q := by
      funext s
      by_cases h : 0 ≤ s
      · simp [h, not_lt.mpr h]
      · simp [h, not_le.mp h]
    have h := hqge.tsum_add hqneg
    rw [heq, hq_sum.tsum_eq] at h
    linarith
  have hqsh_eq : (∑' s : ℤ, if 0 < s then q (s - 1) else 0) = (∑' s : ℤ, if 0 ≤ s then q s else 0) := by
    have h := Equiv.tsum_eq (Equiv.subRight (1:ℤ)) (fun t : ℤ => if 0 ≤ t then q t else 0)
    rw [← h]
    congr 1
    funext s
    simp only [Equiv.subRight_apply]
    by_cases hs : 0 < s
    · rw [if_pos hs, if_pos (show (0:ℤ) ≤ s - 1 from by omega)]
    · rw [if_neg hs, if_neg (show ¬ (0:ℤ) ≤ s - 1 from by omega)]
  have hqnz_split : (∑' s : ℤ, if s ≠ 0 then q s else 0)
      = (∑' s : ℤ, if 0 < s then q s else 0) + (∑' s : ℤ, if s < 0 then q s else 0) := by
    rw [← hqpos.tsum_add hqneg]
    congr 1
    funext s
    rcases lt_trichotomy s 0 with h | h | h
    · rw [if_neg (not_lt.mpr (le_of_lt h)), if_pos h, if_pos (ne_of_lt h)]; ring
    · subst h; simp
    · rw [if_pos h, if_neg (not_lt.mpr (le_of_lt h)), if_pos (ne_of_gt h)]; ring
  have hqnz_le : (∑' s : ℤ, if s ≠ 0 then q s else 0) ≤ (∑' s : ℤ, |(s:ℝ)| * q s) := by
    apply Summable.tsum_le_tsum (fun s => ?_) hqnz hq_mom
    by_cases h : s = 0
    · subst h; simp
    · rw [if_pos h]
      have h1 : (1:ℝ) ≤ |(s:ℝ)| := by
        rw [← Int.cast_abs]
        have := Int.one_le_abs h
        exact_mod_cast this
      calc q s = 1 * q s := by ring
        _ ≤ |(s:ℝ)| * q s := mul_le_mul_of_nonneg_right h1 (hq_nonneg s)
  have hpt : (fun s : ℤ => if s ≤ 0 then p * q s else (1 - p) * q (s - 1))
      = (fun s : ℤ => p * (if s ≤ 0 then q s else 0) + (1 - p) * (if 0 < s then q (s - 1) else 0)) := by
    funext s
    by_cases h : s ≤ 0
    · rw [if_pos h, if_pos h, if_neg (not_lt.mpr h)]; ring
    · rw [if_neg h, if_neg h, if_pos (not_le.mp h)]; ring
  have hsumm_g : Summable (fun s : ℤ => if s ≤ 0 then p * q s else (1 - p) * q (s - 1)) := by
    rw [hpt]
    exact (hqm.mul_left p).add (hqsh.mul_left (1 - p))
  have hsumm_max : Summable (fun s : ℤ => max (p * q s) ((1 - p) * q (s - 1))) := by
    have hrhs : Summable (fun s : ℤ => p * q s + (1 - p) * q (s - 1)) :=
      (hq.mul_left p).add (hqshift.mul_left (1 - p))
    apply Summable.of_nonneg_of_le (fun s => ?_) (fun s => ?_) hrhs
    · have ha : 0 ≤ p * q s := mul_nonneg hp0.le (hq_nonneg s)
      exact le_trans ha (le_max_left _ _)
    · have ha : 0 ≤ p * q s := mul_nonneg hp0.le (hq_nonneg s)
      have hb : 0 ≤ (1 - p) * q (s - 1) := mul_nonneg h1p (hq_nonneg (s - 1))
      exact max_le (le_add_of_nonneg_right hb) (le_add_of_nonneg_left ha)
  have h_g_max : (∑' s : ℤ, if s ≤ 0 then p * q s else (1 - p) * q (s - 1))
      ≤ ∑' s : ℤ, max (p * q s) ((1 - p) * q (s - 1)) := by
    apply Summable.tsum_le_tsum (fun s => ?_) hsumm_g hsumm_max
    by_cases h : s ≤ 0
    · rw [if_pos h]; exact le_max_left _ _
    · rw [if_neg h]; exact le_max_right _ _
  have h_tsum_g : (∑' s : ℤ, if s ≤ 0 then p * q s else (1 - p) * q (s - 1))
      = p * (∑' s : ℤ, if s ≤ 0 then q s else 0) + (1 - p) * (∑' s : ℤ, if 0 < s then q (s - 1) else 0) := by
    rw [hpt, (hqm.mul_left p).tsum_add (hqsh.mul_left (1 - p)), tsum_mul_left, tsum_mul_left]
  have h_g_value : (∑' s : ℤ, if s ≤ 0 then p * q s else (1 - p) * q (s - 1))
      = p * (1 - ∑' s : ℤ, (if 0 < s then q s else 0)) + (1 - p) * (1 - ∑' s : ℤ, (if s < 0 then q s else 0)) := by
    rw [h_tsum_g, hqm_split, hqsh_eq, hqge_split]
  have hPn0 : 0 ≤ (∑' s : ℤ, (if s < 0 then q s else 0)) :=
    tsum_nonneg (fun s => by split_ifs <;> simp [hq_nonneg])
  have hkey : (1 - p * (∑' s : ℤ, |(s:ℝ)| * q s))
      ≤ p * (1 - ∑' s : ℤ, (if 0 < s then q s else 0)) + (1 - p) * (1 - ∑' s : ℤ, (if s < 0 then q s else 0)) := by
    nlinarith [hqnz_split, hqnz_le, hPn0, hp, hp1]
  have h_opt_val : biased_bit_optimal_vulnerability p c = 1 - p * c :=
    (biased_bit_cost_vulnerability_initial_segment p c hp hp1 hc0.le hc).1
  have h_vuln_eq : biased_bit_vulnerability p q = 1 - p * c := by
    rw [hq_opt, h_opt_val]
  have h_vuln_def : biased_bit_vulnerability p q = ∑' s : ℤ, max (p * q s) ((1 - p) * q (s - 1)) := rfl
  have h_chain_le : 1 - p * c ≤ 1 - p * (∑' s : ℤ, |(s : ℝ)| * q s) := by
    nlinarith [hq_cost, hp0]
  have h_chain_eq : 1 - p * (∑' s : ℤ, |(s : ℝ)| * q s) = 1 - p * c := by
    linarith [h_chain_le, hkey, h_g_value, h_g_max, h_vuln_def, h_vuln_eq]
  have h_p_mul : p * (∑' s : ℤ, |(s : ℝ)| * q s) = p * c := by
    linarith [h_chain_eq]
  have h_cost_eq : (∑' s : ℤ, |(s : ℝ)| * q s) = c :=
    mul_left_cancel₀ hp0.ne' h_p_mul
  have h_mid_eq : p * (1 - ∑' s : ℤ, (if 0 < s then q s else 0)) + (1 - p) * (1 - ∑' s : ℤ, (if s < 0 then q s else 0))
      = 1 - p * (∑' s : ℤ, |(s : ℝ)| * q s) := by
    linarith [hkey, h_g_value, h_g_max, h_vuln_def, h_vuln_eq, h_chain_eq]
  have h2p : 0 < 2 * p - 1 := by linarith
  have h_diff : (p * (1 - ∑' s : ℤ, (if 0 < s then q s else 0)) + (1 - p) * (1 - ∑' s : ℤ, (if s < 0 then q s else 0))) - (1 - p * (∑' s : ℤ, |(s : ℝ)| * q s))
      = p * ((∑' s : ℤ, |(s : ℝ)| * q s) - ((∑' s : ℤ, (if 0 < s then q s else 0)) + (∑' s : ℤ, (if s < 0 then q s else 0)))) + (2 * p - 1) * (∑' s : ℤ, (if s < 0 then q s else 0)) := by ring
  rw [h_mid_eq] at h_diff
  have h_zero : p * ((∑' s : ℤ, |(s : ℝ)| * q s) - ((∑' s : ℤ, (if 0 < s then q s else 0)) + (∑' s : ℤ, (if s < 0 then q s else 0)))) + (2 * p - 1) * (∑' s : ℤ, (if s < 0 then q s else 0)) = 0 := by
    linarith
  have h_le_C : (∑' s : ℤ, (if 0 < s then q s else 0)) + (∑' s : ℤ, (if s < 0 then q s else 0)) ≤ (∑' s : ℤ, |(s : ℝ)| * q s) := by
    rw [← hqnz_split]
    exact hqnz_le
  have h1_nonneg : 0 ≤ p * ((∑' s : ℤ, |(s : ℝ)| * q s) - ((∑' s : ℤ, (if 0 < s then q s else 0)) + (∑' s : ℤ, (if s < 0 then q s else 0)))) := by
    nlinarith
  have h2_nonneg : 0 ≤ (2 * p - 1) * (∑' s : ℤ, (if s < 0 then q s else 0)) := by
    nlinarith [hPn0]
  have h_Pneg_zero : (∑' s : ℤ, (if s < 0 then q s else 0)) = 0 := by
    nlinarith
  have h_C_eq_sum : (∑' s : ℤ, |(s : ℝ)| * q s) = (∑' s : ℤ, (if 0 < s then q s else 0)) + (∑' s : ℤ, (if s < 0 then q s else 0)) := by
    nlinarith
  have h_C_eq_nz : (∑' s : ℤ, |(s : ℝ)| * q s) = (∑' s : ℤ, if s ≠ 0 then q s else 0) := by
    rw [hqnz_split, h_C_eq_sum]
  have h_neg : ∀ s < 0, q s = 0 := by
    have h_nonneg_neg : ∀ s : ℤ, 0 ≤ (if s < 0 then q s else 0) := by
      intro s; split_ifs <;> simp [hq_nonneg]
    have h_zero_fun : (fun s : ℤ => if s < 0 then q s else 0) = 0 := by
      have h_has : HasSum (fun s : ℤ => if s < 0 then q s else 0) 0 := by
        have h_sum := hqneg.hasSum
        rwa [h_Pneg_zero] at h_sum
      exact (hasSum_zero_iff_of_nonneg h_nonneg_neg).mp h_has
    intro s hs
    have h_app := congr_fun h_zero_fun s
    simp only [Pi.zero_apply] at h_app
    rw [if_pos hs] at h_app
    exact h_app
  have h_ge2 : ∀ s ≥ 2, q s = 0 := by
    have hf_nonneg : ∀ s : ℤ, 0 ≤ |(s : ℝ)| * q s - (if s ≠ 0 then q s else 0) := by
      intro s
      by_cases hs : s = 0
      · subst hs; simp
      · rw [if_pos hs]
        have h1 : (1 : ℝ) ≤ |(s : ℝ)| := by
          rw [← Int.cast_abs]
          have := Int.one_le_abs hs
          exact_mod_cast this
        have : q s ≤ |(s : ℝ)| * q s := by
          calc q s = 1 * q s := by ring
            _ ≤ |(s : ℝ)| * q s := mul_le_mul_of_nonneg_right h1 (hq_nonneg s)
        linarith
    have hf_summable : Summable (fun s : ℤ => |(s : ℝ)| * q s - (if s ≠ 0 then q s else 0)) :=
      hq_mom.sub hqnz
    have hf_tsum : (∑' s : ℤ, (|(s : ℝ)| * q s - (if s ≠ 0 then q s else 0))) = 0 := by
      rw [hq_mom.tsum_sub hqnz, h_C_eq_nz, sub_self]
    have hf_zero : (fun s : ℤ => |(s : ℝ)| * q s - (if s ≠ 0 then q s else 0)) = 0 := by
      have h_has : HasSum (fun s : ℤ => |(s : ℝ)| * q s - (if s ≠ 0 then q s else 0)) 0 := by
        have h_sum := hf_summable.hasSum
        rwa [hf_tsum] at h_sum
      exact (hasSum_zero_iff_of_nonneg hf_nonneg).mp h_has
    intro s hs
    have h_app := congr_fun hf_zero s
    simp only [Pi.zero_apply] at h_app
    have hs_ne : s ≠ 0 := by omega
    rw [if_pos hs_ne] at h_app
    have hs_abs : |(s : ℝ)| = (s : ℝ) := by
      rw [abs_of_pos]
      exact_mod_cast (by omega : 0 < s)
    rw [hs_abs] at h_app
    have h_mul : ((s : ℝ) - 1) * q s = 0 := by
      linarith [h_app]
    have hs_sub_pos : 0 < (s : ℝ) - 1 := by
      have : (2 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
      linarith
    cases mul_eq_zero.mp h_mul with
    | inl h => linarith
    | inr h => exact h
  have h_supp : ∀ s ∉ ({0, 1} : Finset ℤ), q s = 0 := by
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs
    rcases lt_trichotomy s 0 with h | rfl | h
    · exact h_neg s h
    · exact False.elim (hs.1 rfl)
    · have : 2 ≤ s := by omega
      exact h_ge2 s this
  have h_supp_mom : ∀ s ∉ ({0, 1} : Finset ℤ), |(s : ℝ)| * q s = 0 := by
    intro s hs
    rw [h_supp s hs, mul_zero]
  have h_tsum_mom : (∑' s : ℤ, |(s : ℝ)| * q s) = ∑ s ∈ ({0, 1} : Finset ℤ), |(s : ℝ)| * q s :=
    tsum_eq_sum h_supp_mom
  have h_mom_val : (∑ s ∈ ({0, 1} : Finset ℤ), |(s : ℝ)| * q s) = q 1 := by
    simp
  have h_q1 : q 1 = c := by
    linarith [h_cost_eq, h_tsum_mom, h_mom_val]
  have h_tsum_q : (∑' s : ℤ, q s) = ∑ s ∈ ({0, 1} : Finset ℤ), q s :=
    tsum_eq_sum h_supp
  have h_sum_val : (∑ s ∈ ({0, 1} : Finset ℤ), q s) = q 0 + q 1 := by
    simp
  have h_q0 : q 0 = 1 - c := by
    have h1 : (∑' s : ℤ, q s) = 1 := hq_sum.tsum_eq
    linarith [h1, h_tsum_q, h_sum_val, h_q1]
  funext s
  unfold two_point_mask
  by_cases hs0 : s = 0
  · subst hs0
    simp [h_q0]
  · by_cases hs1 : s = 1
    · subst hs1
      simp [hs0, h_q1]
    · have hs_not : s ∉ ({0, 1} : Finset ℤ) := by
        simp [hs0, hs1]
      simp [hs0, hs1, h_supp s hs_not]
