import AFTD.Prelude
import AFTD.Kb.Tcs.ForestGreedySignedStep

/-!
# forest_greedy_step_neg

Topic: online_algorithms   Node: 06abbe036533

Provenance: helper lemma. Helper for OP-1106, forest greedy carpooling; related background arXiv:2611.00388.

Negating both input discrepancies and flipping the tie coin negates the output of one greedy step.
-/

theorem forest_greedy_step_neg (x y : ℤ) (b : Bool) :
    forest_greedy_signed_step (-x) (-y) (!b) = -forest_greedy_signed_step x y b := by
  cases b <;> simp [forest_greedy_signed_step] <;> split_ifs <;> omega
