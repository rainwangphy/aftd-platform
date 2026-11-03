import AFTD.Prelude
import AFTD.Kb.Tcs.CycleGreedyS

/-!
# cycle_greedy_s_two

Topic: online_algorithms   Node: 9b6085481ab6

Provenance: helper lemma. arXiv:2610.15776, Theorem 9

The rational Cayley product sum evaluates to 3/2 at n = 2: `cycle_greedy_s 2 = 3 / 2`.
-/

/-- Evaluation of the Cayley product sum S_2 = 3/2. -/
theorem cycle_greedy_s_two : cycle_greedy_s 2 = 3 / 2 := by
  unfold cycle_greedy_s
  norm_num [Finset.sum_range_succ, Finset.prod_Icc_succ_top]
