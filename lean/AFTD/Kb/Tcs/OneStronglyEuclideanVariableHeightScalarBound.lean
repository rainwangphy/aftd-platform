import AFTD.Prelude

/-!
# one_strongly_euclidean_variable_height_scalar_bound

Topic: algorithms   Node: e8d1246b6e17

Provenance: helper lemma. OP-1304: scalar bound for the variable-height spherical extension.

For q at least one and z nonnegative, q(1+2z) is at most sqrt(q) times q+2z+2z².
-/

theorem one_strongly_euclidean_variable_height_scalar_bound (q z : ℝ) (hq : 1 ≤ q) (hz : 0 ≤ z) :
    q*(1+2*z) ≤ Real.sqrt q*(q+2*z+2*z^2) := by
  let Q := Real.sqrt q
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    exact Real.one_le_sqrt.mpr hq
  have hQ2 : Q^2 = q := Real.sq_sqrt (by linarith)
  have h1 : 0 ≤ (Q^2-1)/2 := by nlinarith
  have h2 : 0 ≤ 2*(z-(Q-1)/2)^2 := by positivity
  have h3 : 0 ≤ Q*((Q^2-1)/2+2*(z-(Q-1)/2)^2) := by positivity
  change q*(1+2*z) ≤ Q*(q+2*z+2*z^2)
  rw [← hQ2]
  nlinarith
