import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ChoreRemainingSet
import AFTD.Kb.GameTheoryEconomics.FloorLeCeilDivIff

/-!
# chore_remaining_set_two_mul_eq_empty

Topic: fair_division   Node: 066f1e342315

Provenance: helper lemma. arXiv:2611.04884, Section 4, line 729

For every natural number $n$, the set of remaining chores after $2n$ chores have been assigned (out of $2n$ total chores) is empty.
-/

/-- The remaining chores set is empty when there are exactly 2n chores. -/
lemma chore_remaining_set_two_mul_eq_empty (n : ℕ) :
    chore_remaining_set (2 * n) n = ∅ := by first | exact floor_le_ceil_div_iff | (apply floor_le_ceil_div_iff <;> assumption) | (apply floor_le_ceil_div_iff <;> simp_all) | simpa using floor_le_ceil_div_iff | (simp only [chore_remaining_set] at *; first | exact floor_le_ceil_div_iff | (apply floor_le_ceil_div_iff <;> assumption) | (apply floor_le_ceil_div_iff <;> simp_all) | simpa using floor_le_ceil_div_iff)
