import AFTD.Prelude
import AFTD.Kb.Tcs.DiceGraph
import AFTD.Kb.Tcs.HasDirectedCycle
import AFTD.Kb.Tcs.BeatScore
import AFTD.Kb.Tcs.MinimalAdvantage
import AFTD.Kb.Tcs.Die

/-!
# op744_dice6_has_cycle_six

Topic: combinatorics   Node: 12aa17014974

Provenance: formalization of a published result. Source: arXiv:2610.40321 Thm 1

The relation (dice_graph 6).Adj has a directed simple cycle of length 6, has_directed_cycle (dice_graph 6).Adj 6.
-/

private def op744_dice6_has_cycle_six_die0 : Die 6 := ⟨![0,0,1,4,4,4], by decide⟩
private def op744_dice6_has_cycle_six_die1 : Die 6 := ⟨![0,2,3,3,3,3], by decide⟩
private def op744_dice6_has_cycle_six_die2 : Die 6 := ⟨![1,1,1,2,5,5], by decide⟩
private def op744_dice6_has_cycle_six_die3 : Die 6 := ⟨![0,0,1,4,4,5], by decide⟩
private def op744_dice6_has_cycle_six_die4 : Die 6 := ⟨![0,2,2,3,3,3], by decide⟩
private def op744_dice6_has_cycle_six_die5 : Die 6 := ⟨![1,1,2,2,2,5], by decide⟩
private instance op744_dice6_has_cycle_six_instDecidableEqDie :
    DecidableEq (Die 6) :=
  fun a b => decidable_of_iff (a.val = b.val) Subtype.ext_iff.symm

/-- The 6-sided dice graph contains a directed simple cycle of length 6. -/
theorem op744_dice6_has_cycle_six : has_directed_cycle (dice_graph 6).Adj 6 := by
  refine ⟨by norm_num, fun i =>
    ![op744_dice6_has_cycle_six_die0, op744_dice6_has_cycle_six_die1,
      op744_dice6_has_cycle_six_die2, op744_dice6_has_cycle_six_die3,
      op744_dice6_has_cycle_six_die4, op744_dice6_has_cycle_six_die5] i, by decide, ?_⟩
  intro i
  fin_cases i <;> (simp only [dice_graph]; decide)
