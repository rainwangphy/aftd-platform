import AFTD.Prelude

/-!
# b5_clique_bound_fails_of_exceptional

Topic: graphs   Node: db1dc7f81b76

Provenance: helper lemma. the failure half of b5_clique_bound_iff; extends the example B_5(1,2,1,1,1) after Theorem 3.5 of arXiv:2610.21388 (Stronger spectral bound for clique number)

For (n_0, n_1, n_2, n_3) ∈ {(1,1,1,1), (1,1,1,2), (1,2,1,1)} and every n_4 = e ≥ 1, n^2 (1 - 1/ω)^2 < tr(M^2), i.e. the strong bound fails for B_5.
-/

lemma b5_clique_bound_fails_of_exceptional_case_a (x : ℝ) (hx : 1 ≤ x) :
    (4 + x) ^ 2 * (1 - (x + 2)⁻¹) ^ 2 < (x - 1) ^ 2 + 2 * (3 + x * 4) := by
  have h1 : (1 - (x + 2)⁻¹) = (x+1)/(x+2) := by rw [inv_eq_one_div]; field_simp; ring
  rw [h1, div_pow, ← mul_div_assoc, div_lt_iff₀ (by positivity)]
  have key : ((x - 1) ^ 2 + 2 * (3 + x * 4)) * (x + 2) ^ 2 - (4 + x) ^ 2 * (x + 1) ^ 2 = 2 * x ^ 2 + 12 * x + 12 := by ring
  nlinarith [key, hx, sq_nonneg (x - 1)]

lemma b5_clique_bound_fails_of_exceptional_case_b (x : ℝ) (hx : 1 ≤ x) :
    (5 + x) ^ 2 * (1 - (x + 3)⁻¹) ^ 2 < 1 + (x - 1) ^ 2 + 2 * (5 + x * 5) := by
  have h1 : (1 - (x + 3)⁻¹) = (x+2)/(x+3) := by rw [inv_eq_one_div]; field_simp; ring
  rw [h1, div_pow, ← mul_div_assoc, div_lt_iff₀ (by positivity)]
  have key : (1 + (x - 1) ^ 2 + 2 * (5 + x * 5)) * (x + 3) ^ 2 - (5 + x) ^ 2 * (x + 2) ^ 2 = 4 * x + 8 := by ring
  nlinarith [key, hx]

theorem b5_clique_bound_fails_of_exceptional (a b c d e : ℕ) (he : 1 ≤ e)
    (hx : a = 1 ∧ c = 1 ∧ ((b = 1 ∧ d = 1) ∨ (b = 1 ∧ d = 2) ∨ (b = 2 ∧ d = 1))) :
    ((a : ℝ) + b + c + d + e) ^ 2 * (1 - 1 / ((e + max (max (a + b) (b + d)) (c + d) : ℕ) : ℝ)) ^ 2
      < ((a : ℝ) - 1) ^ 2 + ((b : ℝ) - 1) ^ 2 + ((c : ℝ) - 1) ^ 2 + ((d : ℝ) - 1) ^ 2 + ((e : ℝ) - 1) ^ 2
        + 2 * ((a : ℝ) * b + c * d + b * d + e * (a + b + c + d)) := by
  obtain ⟨ha, hc, h⟩ := hx
  subst ha; subst hc
  have he' : (1:ℝ) ≤ (e:ℝ) := by exact_mod_cast he
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · norm_num [max_def]
    exact b5_clique_bound_fails_of_exceptional_case_a (e:ℝ) he'
  · norm_num [max_def]
    exact b5_clique_bound_fails_of_exceptional_case_b (e:ℝ) he'
  · norm_num [max_def]
    exact b5_clique_bound_fails_of_exceptional_case_b (e:ℝ) he'
