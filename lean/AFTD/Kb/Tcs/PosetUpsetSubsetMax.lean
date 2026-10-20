import AFTD.Prelude
import AFTD.Kb.Tcs.PosetUpset
import AFTD.Kb.Tcs.PosetHeightTwo

/-!
# poset_upset_subset_max

Topic: combinatorics   Node: 5b174ce1b2ed

Provenance: helper lemma. arXiv:2610.24774 Section 3.3

In a poset of height two, every element strictly above any element u is maximal.
-/

/-- In a poset of height two, every element in the upset of u is maximal. -/
theorem poset_upset_subset_max {P : Type*} [PartialOrder P]
    (hP : poset_height_two P) (u : P) {y : P} (hy : y ∈ poset_upset u) :
    IsMax y := by
  intro b hyb
  rcases eq_or_lt_of_le hyb with h | h
  · exact le_of_eq h.symm
  · exact absurd ⟨hy, h⟩ (hP u y b)
