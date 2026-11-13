import AFTD.Prelude
import AFTD.Kb.Tcs.HellingerRareSourceRatio
import AFTD.Kb.Tcs.Op1567HellingerRareSourcePolynomialMaximum

/-!
# hellinger_rare_source_ratio_two_max

Topic: information   Node: b9ebcfd0a457

Provenance: helper lemma. arXiv:2610.21231 (On the Subadditivity of Mutual f-Information)

For k = 2, the rare-source Hellinger ratio function hellinger_rare_source_ratio 2 evaluates to (13 + 5 * Real.sqrt 10) / 27 at u_star = (Real.sqrt 10 - 1) / 3, and satisfies hellinger_rare_source_ratio 2 u <= (13 + 5 * Real.sqrt 10) / 27 for all u in Set.Ico 0 1.
-/

/-- The k = 2 rare-source Hellinger ratio attains its maximum (13 + 5 * sqrt 10) / 27 at (sqrt 10 - 1) / 3 -/
theorem hellinger_rare_source_ratio_two_max :
    let u_star : ℝ := (Real.sqrt 10 - 1) / 3
    hellinger_rare_source_ratio 2 u_star = (13 + 5 * Real.sqrt 10) / 27 ∧
    ∀ u ∈ Set.Ico (0 : ℝ) 1, hellinger_rare_source_ratio 2 u ≤ (13 + 5 * Real.sqrt 10) / 27 := by
  intro u_star
  have hu_star_ne_one : u_star ≠ 1 := by
    intro h
    dsimp [u_star] at h
    have h1 : Real.sqrt 10 - 1 = 3 := by linarith
    have h2 : Real.sqrt 10 = 4 := by linarith
    have h3 : (Real.sqrt 10)^2 = 4^2 := by rw [h2]
    rw [Real.sq_sqrt (by norm_num)] at h3
    norm_num at h3
  have hF_eq : ∀ u ≠ (1 : ℝ), hellinger_rare_source_ratio 2 u = (3 + 3 * u - u ^ 2 - u ^ 3) / 4 := by
    intro u hu
    unfold hellinger_rare_source_ratio
    have h1 : 1 - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
    field_simp
    ring
  rcases op_1567_hellinger_rare_source_polynomial_maximum with ⟨hF_star, hF_le⟩
  constructor
  · rw [hF_eq u_star hu_star_ne_one]
    exact hF_star
  · intro u hu
    rw [hF_eq u (ne_of_lt hu.2)]
    exact hF_le u ⟨hu.1, le_of_lt hu.2⟩
