import AFTD.Prelude
import AFTD.Kb.Tcs.CarpoolPathRequests
import AFTD.Kb.Tcs.CarpoolGreedyTailProbability
import AFTD.Kb.Tcs.CarpoolPathGreedyCubicWitness
import AFTD.Kb.Tcs.Op2130RepeatedPathGreedyConverse
import AFTD.Kb.Tcs.CarpoolGreedyTailCount
import AFTD.Kb.Tcs.CarpoolMaxDiscrepancy
import AFTD.Kb.Tcs.CarpoolGreedyOrientations

/-!
# carpool_path_greedy_cubic_tail_lower

Topic: online_algorithms   Node: ea4b17a876f1

Provenance: original. Related work: OP-2130, proposed here; arXiv:2609.21348 Theorem 1.1 gives a deterministic bound for greedy, while arXiv:2611.00388 proves a cubic tail for a different randomized algorithm.

There is a positive absolute constant C such that, for every natural D at least one, a fixed request sequence on the 2D-vertex path of length at most D^3 makes the fair-coin greedy maximum absolute prefix discrepancy reach D with probability at least exp(-C D^3).
-/

theorem carpool_path_greedy_cubic_tail_lower : ∃ C : ℝ, 0 < C ∧ ∀ D : ℕ, 1 ≤ D → ∃ edges : List (Fin (2*D) × Fin (2*D)), carpool_path_requests (2*D) edges ∧ edges.length ≤ D^3 ∧ Real.exp (-C * (D : ℝ)^3) ≤ carpool_greedy_tail_probability (2*D) edges D := by
  obtain ⟨C, hC, h⟩ := op_2130_repeated_path_greedy_converse
  refine ⟨C, hC, fun D hD => ?_⟩
  obtain ⟨edges, hadj, hlen, hp⟩ := h D hD
  refine ⟨edges, fun e he => SimpleGraph.pathGraph_adj.mp (hadj e he), hlen, ?_⟩
  unfold carpool_greedy_tail_probability carpool_greedy_tail_count
  exact hp
