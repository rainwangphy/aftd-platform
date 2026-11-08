import AFTD.Prelude
import AFTD.Kb.Tcs.RectilinearCrossingNumber

/-!
# rectilinear_crossing_number_empty

Topic: combinatorics   Node: 53bcd6fe5170

Provenance: helper lemma. folklore

The rectilinear crossing number of the empty set of points in the real plane ℝ × ℝ is 0.
-/

/-- Sanity lemma: the rectilinear crossing number of the empty point set in ℝ × ℝ is 0. -/
theorem rectilinear_crossing_number_empty : rectilinear_crossing_number ∅ = 0 := by
  have h1 : Finset.powersetCard 2 (∅ : Finset (ℝ × ℝ)) = ∅ := by
    rw [Finset.powersetCard_eq_empty]
    decide
  have h2 : Finset.powersetCard 2 (∅ : Finset (Finset (ℝ × ℝ))) = ∅ := by
    rw [Finset.powersetCard_eq_empty]
    decide
  unfold rectilinear_crossing_number
  rw [h1, h2]
  simp
