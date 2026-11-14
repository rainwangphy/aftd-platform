import AFTD.Prelude

/-!
# energy_filter_gaussian_lower_step

Topic: statistical_mechanics   Node: ceab87acda81

Provenance: helper lemma. OP-892: centered binomial fourth-mass asymptotic via rescaled step functions and dominated convergence.

For n>0, t≥0, and t+1≤n, exp(−((t+1)²/(n−t)−t²/(n−t+1))) is at most (n−t)/(n+t+1).
-/

theorem energy_filter_gaussian_lower_step (n t : ℝ)
    (hn : 0 < n) (ht : 0 ≤ t) (htn : t + 1 ≤ n) :
    Real.exp (-(((t+1)^2/(n-t))-(t^2/(n-t+1)))) ≤ (n-t)/(n+t+1) := by
  have hp : 0 < n-t := by linarith
  have hp' : 0 < n-t+1 := by linarith
  have hdiv : t^2/(n-t+1) ≤ t^2/(n-t) :=
    div_le_div_of_nonneg_left (sq_nonneg t) hp (by linarith)
  have hdelta : (2*t+1)/(n-t) ≤ (t+1)^2/(n-t) - t^2/(n-t+1) := by
    have hpoly : (t+1)^2 = t^2 + (2*t+1) := by ring
    rw [hpoly]
    simp only [add_div]
    linarith
  have hz : 0 < 1+(2*t+1)/(n-t) := by positivity
  have hid : (n-t)/(n+t+1) = 1/(1+(2*t+1)/(n-t)) := by field_simp; ring
  have hexp : 1+(2*t+1)/(n-t) ≤ Real.exp ((2*t+1)/(n-t)) := by
    linarith [Real.add_one_le_exp ((2*t+1)/(n-t))]
  calc
    _ ≤ Real.exp (-((2*t+1)/(n-t))) := by apply Real.exp_le_exp.mpr; linarith
    _ = 1 / Real.exp ((2*t+1)/(n-t)) := by rw [Real.exp_neg, one_div]
    _ ≤ 1 / (1+(2*t+1)/(n-t)) := one_div_le_one_div_of_le hz hexp
    _ = _ := hid.symm
