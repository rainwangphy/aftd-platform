import AFTD.Prelude
import AFTD.Kb.Tcs.CarpoolGreedyTailCount

/-!
# carpool_greedy_tail_probability

Topic: online_algorithms   Node: 38a3508cfee5

Provenance: helper lemma. OP-2130, proposed here; arXiv:2609.21348 Theorem 1.1 gives a deterministic bound for greedy, while arXiv:2611.00388 proves a cubic tail for a different randomized algorithm.

The probability of the greedy maximum-prefix-discrepancy event under independent fair coins, computed as its number of successful length-T coin tapes divided by 2^T.
-/

noncomputable def carpool_greedy_tail_probability (n : ℕ) (edges : List (Fin n × Fin n)) (D : ℕ) : ℝ := (carpool_greedy_tail_count n edges D : ℝ) / (2 ^ edges.length : ℝ)
