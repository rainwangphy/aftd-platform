import AFTD.Prelude

/-!
# energy_filter_gaussian_upper_step

Topic: statistical_mechanics   Node: 171ca29bbeeb

Provenance: helper lemma. OP-892: centered binomial fourth-mass asymptotic via rescaled step functions and dominated convergence.

For n>0, t≥0, and t+1≤n, (n−t)/(n+t+1) is at most exp(−((t+1)²/(n+t+1)−t²/(n+t))).
-/

theorem energy_filter_gaussian_upper_step (n t : ℝ)
    (hn : 0 < n) (ht : 0 ≤ t) (_htn : t + 1 ≤ n) :
    (n-t)/(n+t+1) ≤
      Real.exp (-(((t+1)^2/(n+t+1))-(t^2/(n+t)))) := by
  have hp : 0 < n+t := by positivity
  have hp' : 0 < n+t+1 := by positivity
  have hdiv : t^2/(n+t+1) ≤ t^2/(n+t) :=
    div_le_div_of_nonneg_left (sq_nonneg t) hp (by linarith)
  have hdelta : (t+1)^2/(n+t+1) - t^2/(n+t) ≤ (2*t+1)/(n+t+1) := by
    have hpoly : (t+1)^2 = t^2 + (2*t+1) := by ring
    rw [hpoly, add_div]
    linarith
  have hid : (n-t)/(n+t+1) = 1 - (2*t+1)/(n+t+1) := by field_simp; ring
  have hexp := Real.add_one_le_exp (-((2*t+1)/(n+t+1)))
  calc
    _ = 1 - (2*t+1)/(n+t+1) := hid
    _ ≤ Real.exp (-((2*t+1)/(n+t+1))) := by linarith
    _ ≤ Real.exp (-(((t+1)^2/(n+t+1))-(t^2/(n+t)))) := by
      apply Real.exp_le_exp.mpr
      linarith
