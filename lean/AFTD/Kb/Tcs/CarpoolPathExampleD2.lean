import AFTD.Prelude
import AFTD.Kb.Tcs.CarpoolPathRequests
import AFTD.Kb.Tcs.CarpoolGreedyTailCount

/-!
# carpool_path_example_d2

Topic: online_algorithms   Node: 9d4ab3ef8f76

Provenance: helper lemma. OP-2130, proposed here; arXiv:2609.21348 Theorem 1.1 gives a deterministic bound for greedy, while arXiv:2611.00388 proves a cubic tail for a different randomized algorithm.

For the displayed three requests on the four-vertex path, exactly four of the eight coin tapes reach absolute prefix discrepancy two.
-/

theorem carpool_path_example_d2 : carpool_path_requests 4 [(0,1),(2,3),(1,2)] ∧ carpool_greedy_tail_count 4 [(0,1),(2,3),(1,2)] 2 = 4 := by
  constructor
  · simp [carpool_path_requests]
  · rfl
