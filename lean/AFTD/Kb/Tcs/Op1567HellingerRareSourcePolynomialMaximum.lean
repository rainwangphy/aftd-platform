import AFTD.Prelude

/-!
# op_1567_hellinger_rare_source_polynomial_maximum

Topic: information   Node: 49ffc8e91cec

Provenance: helper lemma. scout/2610-21231-on-the-subadditivity-of-mutual-f-information.md:123

The rare-source ratio polynomial F(u) = (3 + 3 * u - u ^ 2 - u ^ 3) / 4 evaluated at u_star = (Real.sqrt 10 - 1) / 3 equals (13 + 5 * Real.sqrt 10) / 27, and for all u in the closed interval [0, 1], F(u) ≤ (13 + 5 * Real.sqrt 10) / 27.
-/

/-- The candidate limiting polynomial attains its maximum (13+5*sqrt(10))/27 on [0, 1] at u* = (sqrt(10)-1)/3. -/
theorem op_1567_hellinger_rare_source_polynomial_maximum :
    let F : ℝ → ℝ := fun u => (3 + 3 * u - u ^ 2 - u ^ 3) / 4
    let u_star : ℝ := (Real.sqrt 10 - 1) / 3
    F u_star = (13 + 5 * Real.sqrt 10) / 27 ∧
    ∀ u ∈ Set.Icc (0 : ℝ) 1, F u ≤ (13 + 5 * Real.sqrt 10) / 27 := by
  dsimp only
  constructor
  · have hsq : (Real.sqrt 10)^2 = 10 := Real.sq_sqrt (by norm_num)
    have hcube : (Real.sqrt 10)^3 = 10 * Real.sqrt 10 := by
      calc (Real.sqrt 10)^3 = Real.sqrt 10 * (Real.sqrt 10)^2 := by ring
        _ = Real.sqrt 10 * 10 := by rw [hsq]
        _ = 10 * Real.sqrt 10 := by ring
    field_simp
    ring_nf
    rw [hcube]
    ring
  · intro u hu
    have hsq : (Real.sqrt 10)^2 = 10 := Real.sq_sqrt (by norm_num)
    have hcube : (Real.sqrt 10)^3 = 10 * Real.sqrt 10 := by
      calc (Real.sqrt 10)^3 = Real.sqrt 10 * (Real.sqrt 10)^2 := by ring
        _ = Real.sqrt 10 * 10 := by rw [hsq]
        _ = 10 * Real.sqrt 10 := by ring
    have hkey : 52 + 20 * Real.sqrt 10 - 27 * (3 + 3 * u - u ^ 2 - u ^ 3)
        = 9 * (u - (Real.sqrt 10 - 1) / 3)^2 * (3*u + 1 + 2*Real.sqrt 10) := by
      ring_nf
      rw [hcube, hsq]
      ring
    have hnonneg : 0 ≤ 52 + 20 * Real.sqrt 10 - 27 * (3 + 3*u - u^2 - u^3) := by
      rw [hkey]
      apply mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      nlinarith [Real.sqrt_nonneg 10, hu.1]
    nlinarith
