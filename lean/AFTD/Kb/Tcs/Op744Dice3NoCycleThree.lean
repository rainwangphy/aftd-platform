import AFTD.Prelude
import AFTD.Kb.Tcs.DiceGraph
import AFTD.Kb.Tcs.HasDirectedCycle
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.MinimalAdvantage
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.BeatScore
import AFTD.Kb.Tcs.Die

/-!
# op744_dice3_no_cycle_three

Topic: combinatorics   Node: cb12d6bf19e8

Provenance: formalization of a published result. Source: arXiv:2610.40321 Sec 2

The relation (dice_graph 3).Adj contains no directed simple cycle of length 3, that is, ¬ has_directed_cycle (dice_graph 3).Adj 3.
-/

set_option maxRecDepth 5000

instance op744_dice3_no_cycle_three_decidableEq_die3 : DecidableEq (Die 3) :=
  inferInstanceAs (DecidableEq { d : Fin 3 → Fin 3 // Monotone d })

instance op744_dice3_no_cycle_three_fintype_die3 : Fintype (Die 3) :=
  inferInstanceAs (Fintype { d : Fin 3 → Fin 3 // Monotone d })

instance op744_dice3_no_cycle_three_decidable_adj (n : ℕ) (x y : Die n) : Decidable ((dice_graph n).Adj x y) :=
  inferInstanceAs (Decidable (beat_score x y = minimal_advantage n))

/-- The 3-sided dice graph has no directed simple cycle of length 3. -/
theorem op744_dice3_no_cycle_three : ¬ has_directed_cycle (dice_graph 3).Adj 3 := by
  unfold has_directed_cycle
  decide
