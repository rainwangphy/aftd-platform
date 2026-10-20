import AFTD.Prelude
import AFTD.Kb.Tcs.PosetHeightTwo
import AFTD.Kb.Tcs.PosetDownset

/-!
# poset_downset_subset_min

Topic: combinatorics   Node: 339aa2d74d9c

Provenance: helper lemma. arXiv:2610.24774 Section 3.3

In a poset of height two, every element strictly below any element v is minimal.
-/

/-- In a poset of height two, every element in the downset of v is minimal. -/
theorem poset_downset_subset_min {P : Type*} [PartialOrder P]
    (hP : poset_height_two P) (v : P) {x : P} (hx : x ∈ poset_downset v) :
    IsMin x := by
  rw [isMin_iff_forall_not_lt]
  intro y hy
  exact hP y x v ⟨hy, hx⟩
