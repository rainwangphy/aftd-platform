import AFTD.Prelude
import AFTD.Kb.Tcs.IsBox

/-!
# is_box_card

Topic: combinatorics   Node: 713fdb37b1ee

Provenance: helper lemma. arXiv:2611.17378, Section 1

If a finset of points in `Fin d → Fin n` is a box, then its cardinality is `2 ^ d`.
-/

/-- Every box in dimension `d` has exactly `2^d` points. -/
lemma is_box_card (d : ℕ) {n : ℕ} {B : Finset (Fin d → Fin n)} (hB : is_box d B) : B.card = 2 ^ d := by
  rcases hB with ⟨A, hA, rfl⟩
  rw [Fintype.card_piFinset]
  simp [hA]
