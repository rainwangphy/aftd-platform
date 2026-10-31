import AFTD.Prelude
import AFTD.Kb.Tcs.DiceGraph
import AFTD.Kb.Tcs.HasDirectedCycle
import AFTD.Kb.Tcs.Die
import AFTD.Kb.Tcs.BeatScore
import AFTD.Kb.Tcs.MinimalAdvantage

/-!
# op744_dice11_has_directed_cycle_ge_twelve

Topic: combinatorics   Node: 2741b316b3a7

Provenance: formalization of a published result. Source: arXiv:2610.40321 Sec 3

There exists an integer k ≥ 12 such that has_directed_cycle (dice_graph 11).Adj k holds.
-/

private def op744_dice11_die0 : Die 11 := ⟨![0, 2, 3, 3, 3, 6, 6, 6, 6, 10, 10], by decide⟩
private def op744_dice11_die1 : Die 11 := ⟨![2, 2, 2, 2, 2, 4, 7, 7, 9, 9, 9], by decide⟩
private def op744_dice11_die2 : Die 11 := ⟨![0, 1, 1, 4, 5, 5, 6, 6, 8, 9, 10], by decide⟩
private def op744_dice11_die3 : Die 11 := ⟨![1, 3, 3, 4, 4, 4, 4, 4, 9, 9, 10], by decide⟩
private def op744_dice11_die4 : Die 11 := ⟨![0, 1, 2, 2, 2, 6, 6, 7, 9, 10, 10], by decide⟩
private def op744_dice11_die5 : Die 11 := ⟨![0, 0, 4, 5, 5, 5, 5, 5, 7, 9, 10], by decide⟩
private def op744_dice11_die6 : Die 11 := ⟨![1, 3, 3, 3, 3, 4, 5, 7, 7, 9, 10], by decide⟩
private def op744_dice11_die7 : Die 11 := ⟨![1, 1, 1, 2, 2, 3, 9, 9, 9, 9, 9], by decide⟩
private def op744_dice11_die8 : Die 11 := ⟨![1, 1, 3, 3, 4, 6, 7, 7, 7, 8, 8], by decide⟩
private def op744_dice11_die9 : Die 11 := ⟨![1, 2, 2, 2, 2, 4, 6, 6, 10, 10, 10], by decide⟩
private def op744_dice11_die10 : Die 11 := ⟨![0, 0, 1, 3, 4, 7, 8, 8, 8, 8, 8], by decide⟩
private def op744_dice11_die11 : Die 11 := ⟨![2, 3, 3, 4, 4, 4, 4, 7, 7, 7, 10], by decide⟩
private instance op744_dice11_instDecidableEqDie : DecidableEq (Die 11) :=
  fun a b => decidable_of_iff (a.val = b.val) Subtype.ext_iff.symm

/-- Existence of a simple directed cycle of length at least 12 in the 11-sided dice graph. -/
theorem op744_dice11_has_directed_cycle_ge_twelve : ∃ k ≥ 12, has_directed_cycle (dice_graph 11).Adj k := by
  set_option maxRecDepth 100000 in
  refine ⟨12, le_rfl, by norm_num, fun i =>
    ![op744_dice11_die0, op744_dice11_die1, op744_dice11_die2, op744_dice11_die3,
      op744_dice11_die4, op744_dice11_die5, op744_dice11_die6, op744_dice11_die7,
      op744_dice11_die8, op744_dice11_die9, op744_dice11_die10, op744_dice11_die11] i,
    by decide +kernel, ?_⟩
  intro i
  fin_cases i <;> (simp only [dice_graph]; decide +kernel)
