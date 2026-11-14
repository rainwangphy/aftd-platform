import AFTD.Prelude

/-!
# energy_filter_sequence_binomial_gaussian_domination_false

Topic: statistical_mechanics   Node: c383a4eb1230

Provenance: helper lemma. Refutes energy_filter_sequence_binomial_gaussian_domination, a helper proposed for OP-892.

There is no positive real C such that, for every natural k ≥ 1 and every integer s, the binomial coefficient with the negative index clamped by Int.toNat satisfies the stated Gaussian upper bound.
-/

theorem energy_filter_sequence_binomial_gaussian_domination_false :
    ¬ (∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k → ∀ s : ℤ,
      (Nat.choose (2 * k) ((k : ℤ) + s).toNat : ℝ) * Real.sqrt (Real.pi * (k : ℝ)) /
        (2 : ℝ) ^ (2 * k) ≤ C * Real.exp (-((s : ℝ) ^ 2 / (k : ℝ)))) := by
  rintro ⟨C, hC, hbound⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (max (1 : ℝ) (4 * C))
  have hn1 : (1 : ℝ) < n := lt_of_le_of_lt (le_max_left _ _) hn
  have hnC : 4 * C < n := lt_of_le_of_lt (le_max_right _ _) hn
  have hn_nat : 1 ≤ n := by exact_mod_cast (le_of_lt hn1)
  have hclamp : ((1 : ℤ) + -(n : ℤ)).toNat = 0 := by
    apply Int.toNat_of_nonpos
    omega
  have hh := hbound 1 (by decide) (-(n : ℤ))
  have hh' : Real.sqrt Real.pi / 4 ≤ C * Real.exp (-((n : ℝ) ^ 2)) := by
    norm_num [hclamp] at hh
    exact hh
  have hsqrt0 : 0 ≤ Real.sqrt Real.pi := Real.sqrt_nonneg _
  have hsqrtsq : (Real.sqrt Real.pi) ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have hsqrt : 1 < Real.sqrt Real.pi := by nlinarith [Real.pi_gt_three]
  have hn2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hexp : 4 * C < Real.exp ((n : ℝ) ^ 2) := by
    have he := Real.add_one_le_exp ((n : ℝ) ^ 2)
    nlinarith
  have hexppos : 0 < Real.exp ((n : ℝ) ^ 2) := Real.exp_pos _
  have hsmall : C * Real.exp (-((n : ℝ) ^ 2)) < (1 / 4 : ℝ) := by
    rw [Real.exp_neg, ← div_eq_mul_inv]
    apply (div_lt_iff₀ hexppos).2
    linarith
  linarith
