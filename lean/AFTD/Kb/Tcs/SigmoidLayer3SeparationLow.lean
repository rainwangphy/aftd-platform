import AFTD.Prelude
import AFTD.Tactic.NumBounds

/-!
# sigmoid_layer3_separation_low

Topic: circuits   Node: 988fd7739ccd

Provenance: helper lemma. scout/2611-21910-new-gate-weight-and-wire-complexity-bounds-for-sigmoid-neur.md:923

If a real value L is at most 1/10, then the sigmoidal output gate sigmoid(4 * (L - 1/2)) is strictly less than 1/4.
-/

/-- Low output separation for the depth-3 circuit's output gate when L <= 1/10. -/
theorem sigmoid_layer3_separation_low (L : ℝ) (hL : L ≤ 1 / 10) :
    Real.sigmoid (4 * (L - 1 / 2)) < 1 / 4 := by
  have h1 : 4 * (L - 1 / 2) ≤ -8 / 5 := by linarith
  have h2 : Real.sigmoid (4 * (L - 1 / 2)) ≤ Real.sigmoid (-8 / 5) := Real.sigmoid_le h1
  have h3 : Real.sigmoid (-8 / 5) < 1 / 4 := by
    rw [Real.sigmoid_def]
    norm_num
    num_ineq
  exact h2.trans_lt h3
