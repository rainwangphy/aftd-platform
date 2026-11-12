import AFTD.Prelude
import AFTD.Kb.Tcs.DedekindNumber
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.LogicFoundations.CslibLogicPLInstInhabitedOfBot
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.InstFintypeOrderHom

/-!
# dedekind_number_pos

Topic: combinatorics   Node: 59d407bdc994

Provenance: helper lemma. arXiv:2611.13887 Section 1

Every Dedekind number is strictly positive.
-/

/-- Every Dedekind number is strictly positive. -/
lemma dedekind_number_pos (n : ℕ) : 0 < dedekind_number n := by
  unfold dedekind_number
  exact Fintype.card_pos
