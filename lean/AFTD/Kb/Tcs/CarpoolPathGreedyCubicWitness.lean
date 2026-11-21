import AFTD.Prelude
import AFTD.Kb.Tcs.CarpoolPathRequests
import AFTD.Kb.Tcs.CarpoolGreedyOrientations
import AFTD.Kb.Tcs.CarpoolMaxDiscrepancy
import AFTD.Kb.Tcs.Op2130PathCascadeWitness

/-!
# carpool_path_greedy_cubic_witness

Topic: online_algorithms   Node: 2df8f6e6bd52

Provenance: original. Related work: OP-2130, proposed here; arXiv:2609.21348 Theorem 1.1 gives a deterministic greedy upper bound, not this prescribed path construction.

For every natural D at least one, there is a fixed sequence of at most D cubed requests between neighboring vertices of a path with 2D vertices and a length-matched sequence of tie coins such that greedy reaches absolute vertex discrepancy at least D at some prefix. Repeated requests are allowed.
-/

theorem carpool_path_greedy_cubic_witness : ∀ D : ℕ, 1 ≤ D → ∃ edges : List (Fin (2*D) × Fin (2*D)), carpool_path_requests (2*D) edges ∧ edges.length ≤ D^3 ∧ ∃ r : Fin edges.length → Bool, D ≤ carpool_max_discrepancy (2*D) edges (carpool_greedy_orientations (2*D) edges (List.ofFn r)) := by
  intro D hD
  obtain ⟨edges, hadj, hlen, r, hr⟩ := op_2130_path_cascade_witness D hD
  exact ⟨edges, fun e he => SimpleGraph.pathGraph_adj.mp (hadj e he), hlen, r, hr⟩
