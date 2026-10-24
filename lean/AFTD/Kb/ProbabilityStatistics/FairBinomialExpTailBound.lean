import AFTD.Prelude

/-!
# fair_binomial_exp_tail_bound

Topic: concentration   Node: c4d6609fdac6

Provenance: formalization of a published result. Source: scout/2610-16830-the-communication-complexity-of-the-coin-problem.md:333 Theorem 2.7

Let n ≥ 1 be an integer and let X be a binomial random variable with parameters n and 1/2 on a probability space (Ω, μ). For any α ∈ (0,1), the probability that |X - n/2| ≥ α n / 2 is at most 2 * exp(-α^2 * n / 6).
-/

lemma fair_binomial_exp_tail_bound_sum_id (n : ℕ) (t : ℝ) :
    ∑ k ∈ Finset.Iic n,
      ((n.choose k : ℝ) * (1/2:ℝ) ^ k * (1/2:ℝ) ^ (n - k) * Real.exp (t * ((k:ℝ) - (n:ℝ)/2)))
      = Real.cosh (t/2) ^ n := by
  have hsum : ∑ k ∈ Finset.Iic n, ((n.choose k : ℝ) * (Real.exp t)^k) = (1 + Real.exp t)^n := by
    rw [add_comm 1 (Real.exp t), add_pow (Real.exp t) 1 n]
    rw [show Finset.Iic n = Finset.range (n+1) from by ext k; simp]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp only [one_pow, mul_one]
    ring
  have step : ∀ k ∈ Finset.Iic n,
      ((n.choose k : ℝ) * (1/2:ℝ) ^ k * (1/2:ℝ) ^ (n - k) * Real.exp (t * ((k:ℝ) - (n:ℝ)/2)))
      = ((1/2:ℝ)^n * Real.exp (-(t*(n:ℝ)/2))) * ((n.choose k : ℝ) * (Real.exp t)^k) := by
    intro k hk
    have hk' : k ≤ n := Finset.mem_Iic.mp hk
    have hp : (1/2:ℝ)^k * (1/2:ℝ)^(n-k) = (1/2:ℝ)^n := by
      rw [← pow_add, Nat.add_sub_cancel' hk']
    have he : Real.exp (t * ((k:ℝ) - (n:ℝ)/2)) = (Real.exp t)^k * Real.exp (-(t*(n:ℝ)/2)) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    calc (n.choose k : ℝ) * (1/2:ℝ) ^ k * (1/2:ℝ) ^ (n - k) * Real.exp (t * ((k:ℝ) - (n:ℝ)/2))
        = ((1/2:ℝ)^k * (1/2:ℝ)^(n-k)) * (n.choose k : ℝ) * Real.exp (t * ((k:ℝ) - (n:ℝ)/2)) := by ring
      _ = (1/2:ℝ)^n * (n.choose k : ℝ) * ((Real.exp t)^k * Real.exp (-(t*(n:ℝ)/2))) := by rw [hp, he]
      _ = ((1/2:ℝ)^n * Real.exp (-(t*(n:ℝ)/2))) * ((n.choose k : ℝ) * (Real.exp t)^k) := by ring
  rw [Finset.sum_congr rfl step, ← Finset.mul_sum, hsum]
  have h1 : Real.exp (-(t*(n:ℝ)/2)) = (Real.exp (-(t/2)))^n := by
    rw [show -(t * (n:ℝ) / 2) = (n:ℝ) * (-(t/2)) by ring, Real.exp_nat_mul]
  rw [h1, ← mul_pow, ← mul_pow]
  congr 1
  rw [Real.cosh_eq]
  have h2 : Real.exp (-(t/2)) * Real.exp t = Real.exp (t/2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [mul_add, mul_one]
  have h3 : (1/2:ℝ) * Real.exp (-(t/2)) * Real.exp t = 1/2 * Real.exp (t/2) := by
    rw [mul_assoc, h2]
  rw [h3]
  ring

lemma fair_binomial_exp_tail_bound_mgf_eq (n : ℕ) (t : ℝ) :
    ProbabilityTheory.mgf (fun k : ℕ => (k:ℝ) - (n:ℝ)/2)
      (ProbabilityTheory.binomial n ⟨1/2, by norm_num⟩) t = Real.cosh (t/2) ^ n := by
  rw [ProbabilityTheory.mgf, ProbabilityTheory.integral_binomial]
  simp only [smul_eq_mul]
  norm_num
  exact fair_binomial_exp_tail_bound_sum_id n t

open MeasureTheory ProbabilityTheory
open scoped unitInterval
/-- Exponential tail bound for the fair binomial distribution B(n, 1/2). -/
theorem fair_binomial_exp_tail_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 1 ≤ n) (X : Ω → ℕ)
    (hX : HasLaw X (binomial n ⟨1/2, by norm_num⟩) μ)
    (α : ℝ) (hα_pos : 0 < α) (hα_lt_one : α < 1) :
    μ.real {ω | α * (n : ℝ) / 2 ≤ |(X ω : ℝ) - (n : ℝ) / 2|} ≤
      2 * Real.exp (- α ^ 2 * (n : ℝ) / 6) := by
  have hmeas : MeasurableSet {k : ℕ | α * (n:ℝ)/2 ≤ |(k:ℝ) - (n:ℝ)/2|} := by measurability
  rw [hX.measureReal_eq hmeas]
  set ε : ℝ := α * (n:ℝ)/2 with hε
  have hαn : 0 < α^2 * (n:ℝ) := by positivity
  have hsubset : {k : ℕ | ε ≤ |(k:ℝ) - (n:ℝ)/2|}
      ⊆ {k : ℕ | ε ≤ (k:ℝ) - (n:ℝ)/2} ∪ {k : ℕ | (k:ℝ) - (n:ℝ)/2 ≤ -ε} := by
    intro k hk
    simp only [Set.mem_ofPred_eq, Set.mem_union] at hk ⊢
    rcases le_total 0 ((k:ℝ) - (n:ℝ)/2) with h | h
    · exact Or.inl (by rw [abs_of_nonneg h] at hk; exact hk)
    · exact Or.inr (by rw [abs_of_nonpos h] at hk; linarith)
  have hmono : (binomial n ⟨1/2, by norm_num⟩).real {k : ℕ | ε ≤ |(k:ℝ) - (n:ℝ)/2|}
      ≤ (binomial n ⟨1/2, by norm_num⟩).real
        ({k : ℕ | ε ≤ (k:ℝ) - (n:ℝ)/2} ∪ {k : ℕ | (k:ℝ) - (n:ℝ)/2 ≤ -ε}) :=
    measureReal_mono hsubset (measure_ne_top _ _)
  have hunion : (binomial n ⟨1/2, by norm_num⟩).real
      ({k : ℕ | ε ≤ (k:ℝ) - (n:ℝ)/2} ∪ {k : ℕ | (k:ℝ) - (n:ℝ)/2 ≤ -ε})
      ≤ (binomial n ⟨1/2, by norm_num⟩).real {k : ℕ | ε ≤ (k:ℝ) - (n:ℝ)/2}
        + (binomial n ⟨1/2, by norm_num⟩).real {k : ℕ | (k:ℝ) - (n:ℝ)/2 ≤ -ε} :=
    measureReal_union_le _ _
  have hU : (binomial n ⟨1/2, by norm_num⟩).real {k : ℕ | ε ≤ (k:ℝ) - (n:ℝ)/2}
      ≤ Real.exp (-(α^2 * (n:ℝ))) * Real.cosh α ^ n := by
    have hint : Integrable (fun k : ℕ => Real.exp ((2*α) * ((k:ℝ) - (n:ℝ)/2)))
        (binomial n ⟨1/2, by norm_num⟩) := integrable_binomial _
    have h := measure_ge_le_exp_mul_mgf (μ := binomial n ⟨1/2, by norm_num⟩)
      (X := fun k : ℕ => (k:ℝ) - (n:ℝ)/2) (t := 2*α) ε (by positivity) hint
    rw [fair_binomial_exp_tail_bound_mgf_eq] at h
    rw [show (2*α)/2 = α by ring] at h
    rw [show -(2*α) * ε = -(α^2 * (n:ℝ)) by rw [hε]; ring] at h
    exact h
  have hL : (binomial n ⟨1/2, by norm_num⟩).real {k : ℕ | (k:ℝ) - (n:ℝ)/2 ≤ -ε}
      ≤ Real.exp (-(α^2 * (n:ℝ))) * Real.cosh α ^ n := by
    have hint : Integrable (fun k : ℕ => Real.exp ((-(2*α)) * ((k:ℝ) - (n:ℝ)/2)))
        (binomial n ⟨1/2, by norm_num⟩) := integrable_binomial _
    have h := measure_le_le_exp_mul_mgf (μ := binomial n ⟨1/2, by norm_num⟩)
      (X := fun k : ℕ => (k:ℝ) - (n:ℝ)/2) (t := -(2*α)) (-ε) (by linarith) hint
    rw [fair_binomial_exp_tail_bound_mgf_eq] at h
    rw [show (-(2*α))/2 = -α by ring, Real.cosh_neg] at h
    rw [show -(-(2*α)) * (-ε) = -(α^2 * (n:ℝ)) by rw [hε]; ring] at h
    exact h
  have hcosh : Real.cosh α ^ n ≤ Real.exp ((n:ℝ) * (α^2/2)) := by
    calc Real.cosh α ^ n ≤ (Real.exp (α^2/2))^n :=
          pow_le_pow_left₀ (by positivity) (Real.cosh_le_exp_half_sq α) n
      _ = Real.exp ((n:ℝ) * (α^2/2)) := by rw [Real.exp_nat_mul]
  have htail : Real.exp (-(α^2 * (n:ℝ))) * Real.cosh α ^ n
      ≤ Real.exp (- α^2 * (n:ℝ) / 6) := by
    calc Real.exp (-(α^2 * (n:ℝ))) * Real.cosh α ^ n
        ≤ Real.exp (-(α^2 * (n:ℝ))) * Real.exp ((n:ℝ) * (α^2/2)) := by gcongr
      _ = Real.exp (-(α^2 * (n:ℝ)) + (n:ℝ) * (α^2/2)) := by rw [← Real.exp_add]
      _ ≤ Real.exp (- α^2 * (n:ℝ) / 6) := by
          apply Real.exp_le_exp.mpr
          linarith
  linarith
