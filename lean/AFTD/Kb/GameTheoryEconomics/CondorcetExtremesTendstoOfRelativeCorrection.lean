import AFTD.Prelude

/-!
# condorcet_extremes_tendsto_of_relative_correction

Topic: social_choice   Node: b418b4b770db

Provenance: helper lemma. step towards op_1821_condorcet_extremes_sharp_dependence

If the ratio q(n) / p(n)^2 satisfies q(n) / p(n)^2 = (1 - 1/n) * (1 + a(n)) for large n where n * a(n) tends to 0, then n * (1 - q(n) / p(n)^2) tends to 1 as n tends to infinity.
-/

/-- If the ratio q(n) / p(n)^2 satisfies q(n) / p(n)^2 = (1 - 1/n) * (1 + a(n)) where n * a(n) tends to 0, then n * (1 - q(n) / p(n)^2) tends to 1. -/
theorem condorcet_extremes_tendsto_of_relative_correction
    (p q : ℕ → ℝ) (a : ℕ → ℝ)
    (h_ratio : ∀ᶠ n : ℕ in Filter.atTop, q n / (p n ^ 2) = (1 - 1 / (n : ℝ)) * (1 + a n))
    (ha : Filter.Tendsto (fun n : ℕ => (n : ℝ) * a n) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n : ℕ => (n : ℝ) * (1 - q n / (p n ^ 2))) Filter.atTop (nhds 1) := by
  have h_a : Filter.Tendsto (fun n : ℕ => a n) Filter.atTop (nhds 0) := by
    have h_inv : Filter.Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have h := h_inv.mul ha
    have h' : Filter.Tendsto (fun n : ℕ => ((n : ℝ))⁻¹ * ((n : ℝ) * a n))
        Filter.atTop (nhds 0) := by
      simpa using h
    refine h'.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by
      have : n ≠ 0 := by omega
      exact_mod_cast this
    field_simp
  have h_eq : (fun n : ℕ => (n : ℝ) * (1 - q n / (p n ^ 2))) =ᶠ[Filter.atTop]
      (fun n : ℕ => 1 + a n - (n : ℝ) * a n) := by
    filter_upwards [h_ratio, Filter.eventually_ge_atTop 1] with n hratio hn
    rw [hratio]
    have hn0 : (n : ℝ) ≠ 0 := by
      have : n ≠ 0 := by omega
      exact_mod_cast this
    field_simp
    ring
  have h_lim : Filter.Tendsto (fun n : ℕ => 1 + a n - (n : ℝ) * a n)
      Filter.atTop (nhds 1) := by
    have h1 : Filter.Tendsto (fun n : ℕ => 1 + a n) Filter.atTop (nhds (1 + 0)) :=
      (tendsto_const_nhds (x := (1 : ℝ))).add h_a
    have h2 := h1.sub ha
    simpa using h2
  exact h_lim.congr' h_eq.symm
