import AFTD.Prelude
import AFTD.Kb.Tcs.TwoPointMask

/-!
# two_point_mask_moment

Topic: information   Node: 55d82c7151f7

Provenance: helper lemma. arXiv:2611.16066, Theorem 5.5

For any real number c satisfying 0 ≤ c and c ≤ 1, the sum ∑' s : ℤ, |(s : ℝ)| * two_point_mask c s equals c.
-/

/-- The absolute first moment of the two-point mask (1 - c) δ_0 + c δ_1 is c. -/
theorem two_point_mask_moment (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) : (∑' s : ℤ, |(s : ℝ)| * two_point_mask c s) = c := by
  have h : ∀ s ∉ ({0, 1} : Finset ℤ), |(s : ℝ)| * two_point_mask c s = 0 := by
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs
    unfold two_point_mask
    simp [hs.1, hs.2]
  rw [tsum_eq_sum h]
  simp [two_point_mask]
