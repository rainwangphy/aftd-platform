import AFTD.Prelude

/-!
# energy_filter_sequence_central_binom_asymptotic

Topic: statistical_mechanics   Node: 502cf9e4bfc4

Provenance: helper lemma. step towards summable_energy_filters_universal_lattice_purity_constant

The central binomial coefficient satisfies C(2n,n) * sqrt(pi n) / 4^n tending to 1.
-/

/-- Stirling-type asymptotic for the central binomial coefficient, the normalization constant of both trace sums. -/
theorem energy_filter_sequence_central_binom_asymptotic :
    Filter.Tendsto
      (fun n : ℕ => (Nat.choose (2 * n) n : ℝ) * Real.sqrt (Real.pi * (n : ℝ)) / (4 : ℝ) ^ n)
      Filter.atTop (nhds 1) := by
  let F : ℕ → ℝ := fun n => (Nat.choose (2 * n) n : ℝ) * Real.sqrt (Real.pi * (n : ℝ)) / (4 : ℝ) ^ n
  have hchoose (n : ℕ) :
      (Nat.choose (2*n) n : ℝ) * (n.factorial : ℝ) ^ 2 = ((2*n).factorial : ℝ) := by
    have hn : n ≤ 2*n := by omega
    have heq := Nat.choose_mul_factorial_mul_factorial hn
    have hsub : 2*n-n=n := by omega
    rw [hsub] at heq
    have heq' : (Nat.choose (2*n) n : ℝ) * (n.factorial : ℝ) * (n.factorial : ℝ) = ((2*n).factorial : ℝ) := by exact_mod_cast heq
    nlinarith [heq']
  have hpow (n : ℕ) : (2 : ℝ) ^ (4*n) = ((4 : ℝ)^n)^2 := by
    calc
      _ = ((2:ℝ)^4)^n := by rw [pow_mul]
      _ = ((4:ℝ)^2)^n := by norm_num
      _ = _ := by rw [← pow_mul, Nat.mul_comm, pow_mul]
  have hW (n : ℕ) : Real.Wallis.W n = ((4:ℝ)^n)^2 /
      ((Nat.choose (2*n) n : ℝ)^2 * (2*(n:ℝ)+1)) := by
    rw [Real.Wallis.W_eq_factorial_ratio, hpow, ← hchoose]
    have hc : (Nat.choose (2*n) n : ℝ) ≠ 0 := by
      exact_mod_cast Nat.centralBinom_ne_zero n
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    have hd : 2*(n:ℝ)+1 ≠ 0 := by positivity
    field_simp
  have hF2 (n : ℕ) : F n ^ 2 =
      (Real.pi * ((n:ℝ) / (2*(n:ℝ)+1))) / Real.Wallis.W n := by
    have hc : (Nat.choose (2*n) n : ℝ) ≠ 0 := by
      exact_mod_cast Nat.centralBinom_ne_zero n
    have hp : (4:ℝ)^n ≠ 0 := by positivity
    have hd : 2*(n:ℝ)+1 ≠ 0 := by positivity
    have hs : (Real.sqrt (Real.pi * (n:ℝ)))^2 = Real.pi * (n:ℝ) := by
      exact Real.sq_sqrt (by positivity)
    rw [hW]
    dsimp [F]
    field_simp
    nlinarith [hs]
  have hratio : Filter.Tendsto (fun n : ℕ => (Real.pi * ((n:ℝ) / (2*(n:ℝ)+1))) / Real.Wallis.W n)
      Filter.atTop (nhds 1) := by
    have hnum : Filter.Tendsto (fun n : ℕ => Real.pi * ((n:ℝ) / (2*(n:ℝ)+1)))
        Filter.atTop (nhds (Real.pi * (1/2))) :=
      tendsto_const_nhds.mul Stirling.tendsto_self_div_two_mul_self_add_one
    have h := hnum.div
      Real.Wallis.tendsto_W_nhds_pi_div_two (by positivity : Real.pi / 2 ≠ 0)
    have he : Real.pi * (1 / 2) / (Real.pi / 2) = 1 := by
      field_simp [Real.pi_ne_zero]
    rw [he] at h
    exact h
  have hsquare : Filter.Tendsto (fun n => F n ^ 2) Filter.atTop (nhds 1) := by
    convert hratio using 1
    funext n
    exact hF2 n
  have hsqrt : Filter.Tendsto (fun n => Real.sqrt (F n ^ 2)) Filter.atTop (nhds 1) := by
    change Filter.Tendsto ((fun x : ℝ => Real.sqrt x) ∘ fun n => F n ^ 2) Filter.atTop (nhds 1)
    simpa only [Real.sqrt_one] using (Real.continuous_sqrt.tendsto 1).comp hsquare
  have hpos (n : ℕ) : 0 ≤ F n := by dsimp [F]; positivity
  have he : (fun n => Real.sqrt (F n ^ 2)) = F := by
    funext n
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (hpos n)]
  rw [he] at hsqrt
  exact hsqrt
