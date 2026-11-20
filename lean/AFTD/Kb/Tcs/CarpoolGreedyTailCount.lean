import AFTD.Prelude
import AFTD.Kb.Tcs.CarpoolGreedyOrientations
import AFTD.Kb.Tcs.CarpoolMaxDiscrepancy

/-!
# carpool_greedy_tail_count

Topic: online_algorithms   Node: f437118dca1f

Provenance: helper lemma. OP-2130, proposed here; arXiv:2609.21348 Theorem 1.1 gives a deterministic bound for greedy, while arXiv:2611.00388 proves a cubic tail for a different randomized algorithm.

The number of length-T Boolean coin tapes for which the greedy trajectory has maximum absolute prefix discrepancy at least D, where T is the length of the fixed request sequence.
-/

def carpool_greedy_tail_count (n : ℕ) (edges : List (Fin n × Fin n)) (D : ℕ) : ℕ := (Finset.univ.filter (fun r : Fin edges.length → Bool => D ≤ carpool_max_discrepancy n edges (carpool_greedy_orientations n edges (List.ofFn r)))).card
