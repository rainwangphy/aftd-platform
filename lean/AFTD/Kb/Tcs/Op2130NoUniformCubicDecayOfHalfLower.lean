import AFTD.Prelude

/-!
# op_2130_no_uniform_cubic_decay_of_half_lower

Topic: online_algorithms   Node: d2357768c9db

Provenance: helper lemma. Analytic step in the refutation of op_2130_path_greedy_fixed_time_tail

A real-valued function that is at least one half at every positive natural cannot be uniformly bounded above by C exp(-c D cubed) for positive constants c and C.
-/

theorem op_2130_no_uniform_cubic_decay_of_half_lower (F : ℕ → ℝ) (hlower : ∀ D, 1 ≤ D → (1 / 2 : ℝ) ≤ F D) :
    ¬ ∃ (c C : ℝ), 0 < c ∧ 0 < C ∧ ∀ D, 1 ≤ D → F D ≤ C * Real.exp (-c * (D : ℝ)^3) := by
  rintro ⟨c, C, hc, hC, hupper⟩
  obtain ⟨D, hD⟩ := exists_nat_gt (max 1 (2 * C / c))
  have hDreal : (1 : ℝ) < D := lt_of_le_of_lt (le_max_left _ _) hD
  have hDnat : 1 ≤ D := by exact_mod_cast (le_of_lt hDreal)
  have hlarge : 2 * C < c * (D : ℝ) := by
    have hh : 2 * C / c < (D : ℝ) := lt_of_le_of_lt (le_max_right _ _) hD
    nlinarith [(div_lt_iff₀ hc).mp hh]
  have hcube : (D : ℝ) ≤ (D : ℝ)^3 := by
    have hs : 0 ≤ ((D : ℝ) - 1) * ((D : ℝ)^2 + (D : ℝ) + 1) := by positivity
    nlinarith
  have hexp : 2 * C < Real.exp (c * (D : ℝ)^3) := by
    have h1 := Real.add_one_le_exp (c * (D : ℝ)^3)
    have h2 := mul_nonneg (le_of_lt hc) (sub_nonneg.mpr hcube)
    nlinarith
  have ht := le_trans (hlower D hDnat) (hupper D hDnat)
  have hp := mul_le_mul_of_nonneg_right ht (le_of_lt (Real.exp_pos (c * (D : ℝ)^3)))
  have hcancel : (C * Real.exp (-c * (D : ℝ)^3)) * Real.exp (c * (D : ℝ)^3) = C := by
    rw [mul_assoc, ← Real.exp_add]
    simp
  rw [hcancel] at hp
  nlinarith
