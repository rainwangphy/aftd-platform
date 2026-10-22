import AFTD.Prelude
import AFTD.Kb.Tcs.RecursiveLineHoleBudget

/-!
# recursive_line_hole_budget_four_four

Topic: combinatorics   Node: d999b15e6dd2

Provenance: helper lemma. scout/2610-22875-overtake-and-the-recursive-line-equality-for-second-order-z.md:363

The recursive-line hole budget recursive_line_hole_budget 4 4 9 10 is equal to 5.
-/

/-- Sanity check: the recursive-line hole budget at (4,4) with z=9 and z_RL=10 equals 5. -/
theorem recursive_line_hole_budget_four_four :
    recursive_line_hole_budget 4 4 9 10 = 5 := by rfl
