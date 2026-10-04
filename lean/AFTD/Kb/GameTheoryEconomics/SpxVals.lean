import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpxX
import AFTD.Kb.GameTheoryEconomics.SpxW

/-!
# spx_vals

Topic: mechanism_design   Node: 4489dbdbc586

The support values and probabilities of the four-player instance, entry by entry.
-/

/-- The support values and probabilities of the four-player instance. -/
lemma spx_vals :
    spx_x 0 0 = 24 / 5 ∧ spx_x 0 1 = 0 ∧ spx_w 0 0 = 1 ∧ spx_x 1 0 = 9 ∧ spx_x 1 1 = 3 ∧ spx_w 1 0 = 1 / 10 ∧
    spx_x 2 0 = 1000 ∧ spx_x 2 1 = 0 ∧ spx_w 2 0 = 1 / 300 ∧ spx_x 3 0 = 40 ∧ spx_x 3 1 = 0 ∧
    spx_w 3 0 = 1 / 25 := by
  simp [spx_x, spx_w]
