import AFTD.Prelude

/-!
# four_point_set_coprime_inverse_odd

Topic: combinatorics   Node: 1c54ad27db71

Provenance: helper lemma. step towards four_point_set_quadratic_packing_interval

For any integer n, setting a = 2n - 1 and b = 2n + 1, there exists an odd integer gamma such that (a * gamma) % (2 * b) = 1 % (2 * b). Explicitly, gamma = n if n is odd, and gamma = 3n + 1 if n is even.
-/

/-- Existence of an odd integer gamma such that a * gamma is congruent to 1 modulo 2b. -/
theorem four_point_set_coprime_inverse_odd (n : ℤ) :
    let a : ℤ := 2 * n - 1
    let b : ℤ := 2 * n + 1
    ∃ gamma : ℤ, Odd gamma ∧ (a * gamma) % (2 * b) = 1 % (2 * b) := by
  by_cases h : Odd n
  · obtain ⟨k, rfl⟩ := h
    refine ⟨2 * k + 1, ⟨k, by ring⟩, ?_⟩
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
    exact Int.emod_eq_zero_of_dvd ⟨k, by ring⟩
  · have he : Even n := Int.not_odd_iff_even.mp h
    obtain ⟨k, rfl⟩ := he
    refine ⟨3 * (2 * k) + 1, ⟨3 * k, by ring⟩, ?_⟩
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
    exact Int.emod_eq_zero_of_dvd ⟨3 * k - 1, by ring⟩
