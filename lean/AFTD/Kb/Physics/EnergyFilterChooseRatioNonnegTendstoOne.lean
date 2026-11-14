import AFTD.Prelude

/-!
# energy_filter_choose_ratio_nonneg_tendsto_one

Topic: statistical_mechanics   Node: 7c98a62a49c7

Provenance: helper lemma. OP-892: zero-extended centered binomial estimates.

For every fixed natural h, choose(2n,n+h)/choose(2n,n) tends to one.
-/

theorem energy_filter_choose_ratio_nonneg_tendsto_one (h : ℕ) :
    Filter.Tendsto
      (fun n : ℕ => (Nat.choose (2 * n) (n + h) : ℝ) /
        (Nat.choose (2 * n) n : ℝ)) Filter.atTop (nhds 1) := by
  induction h with
  | zero =>
    have hden (n : ℕ) : (Nat.choose (2*n) n : ℝ) ≠ 0 := by
      exact_mod_cast Nat.centralBinom_ne_zero n
    simp only [Nat.add_zero, div_self (hden _)]
    exact tendsto_const_nhds
  | succ h ih =>
    have hfactor : Filter.Tendsto (fun n : ℕ => ((n:ℝ) - h) / ((n:ℝ) + h + 1)) Filter.atTop (nhds 1) := by
      have hlim := tendsto_add_mul_div_add_mul_atTop_nhds (-(h:ℝ)) ((h:ℝ)+1) (1:ℝ) (show (1:ℝ) ≠ 0 by norm_num)
      convert hlim using 1 <;> simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    have heq : ∀ᶠ n : ℕ in Filter.atTop,
        (Nat.choose (2*n) (n+(h+1)) : ℝ) / (Nat.choose (2*n) n : ℝ) =
          ((Nat.choose (2*n) (n+h) : ℝ) / (Nat.choose (2*n) n : ℝ)) *
            (((n:ℝ)-h) / ((n:ℝ)+h+1)) := by
      filter_upwards [Filter.eventually_ge_atTop h] with n hn
      have he := Nat.choose_succ_right_eq (2*n) (n+h)
      have hsub : 2*n-(n+h)=n-h := by omega
      rw [hsub] at he
      have her : (Nat.choose (2*n) (n+h+1) : ℝ) * (((n+h+1 : ℕ) : ℝ)) =
          (Nat.choose (2*n) (n+h) : ℝ) * (((n-h : ℕ) : ℝ)) := by
        exact_mod_cast he
      rw [Nat.cast_add, Nat.cast_add, Nat.cast_one, Nat.cast_sub hn] at her
      have hc : (Nat.choose (2*n) n : ℝ) ≠ 0 := by exact_mod_cast Nat.centralBinom_ne_zero n
      have hd : (n:ℝ)+h+1 ≠ 0 := by positivity
      rw [show n+(h+1)=n+h+1 by omega]
      field_simp
      nlinarith [her]
    have ht := ih.mul hfactor
    simp only [one_mul] at ht
    apply ht.congr'
    filter_upwards [heq] with n hn
    exact hn.symm
