import AFTD.Prelude
import AFTD.Tactic.NumBounds

/-!
# sigmoid_layer3_separation_high

Topic: circuits   Node: 5893d08a87b3

Provenance: helper lemma. scout/2611-21910-new-gate-weight-and-wire-complexity-bounds-for-sigmoid-neur.md:923

If a real value L is at least 9/10, then the sigmoidal output gate sigmoid(4 * (L - 1/2)) strictly exceeds 3/4.
-/

/-- High output separation for the depth-3 circuit's output gate when L >= 9/10. -/
theorem sigmoid_layer3_separation_high (L : ℝ) (hL : 9 / 10 ≤ L) :
    3 / 4 < Real.sigmoid (4 * (L - 1 / 2)) := by
  have h1 : (8 : ℝ) / 5 ≤ 4 * (L - 1 / 2) := by
    linarith
  have h2 : Real.sigmoid (8 / 5) ≤ Real.sigmoid (4 * (L - 1 / 2)) :=
    Real.sigmoid_le h1
  have h3 : (3 : ℝ) / 4 < Real.sigmoid (8 / 5) := by
    rw [Real.sigmoid_def]
    num_ineq
  exact lt_of_lt_of_le h3 h2
