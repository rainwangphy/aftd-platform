import AFTD.Prelude
import AFTD.Kb.Tcs.DiceGraph
import AFTD.Kb.Tcs.HasDirectedCycle
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.BeatScore
import AFTD.Kb.Tcs.MinimalAdvantage
import AFTD.Kb.Tcs.Die

/-!
# op744_dice7_has_cycle_fourteen

Topic: combinatorics   Node: f50c586c318a

Provenance: formalization of a published result. Source: arXiv:2610.40321 Sec 3

The relation (dice_graph 7).Adj has a directed simple cycle of length 14, has_directed_cycle (dice_graph 7).Adj 14.
-/

/-- The 7-sided dice graph contains a directed simple cycle of length 14. -/
theorem op744_dice7_has_cycle_fourteen : has_directed_cycle (dice_graph 7).Adj 14 := by
  let _ : DecidableEq (Die 7) := fun a b => Subtype.instDecidableEq a b
  let c : Fin 14 → Die 7 :=
    ![⟨![0,2,2,2,4,5,5], by decide⟩,
      ⟨![0,1,2,3,3,4,4], by decide⟩,
      ⟨![1,1,1,2,2,3,5], by decide⟩,
      ⟨![0,0,0,2,4,4,5], by decide⟩,
      ⟨![0,0,1,1,3,3,3], by decide⟩,
      ⟨![0,0,2,2,2,2,2], by decide⟩,
      ⟨![1,1,1,1,1,3,5], by decide⟩,
      ⟨![0,0,0,2,4,4,6], by decide⟩,
      ⟨![1,1,1,1,1,1,5], by decide⟩,
      ⟨![0,0,0,3,3,3,4], by decide⟩,
      ⟨![0,1,2,2,2,2,3], by decide⟩,
      ⟨![1,1,1,1,1,6,6], by decide⟩,
      ⟨![0,0,0,4,5,6,6], by decide⟩,
      ⟨![1,3,3,3,4,4,4], by decide⟩]
  refine ⟨by norm_num, c, by decide, ?_⟩
  intro i
  fin_cases i <;> (simp only [dice_graph, c]; decide)
