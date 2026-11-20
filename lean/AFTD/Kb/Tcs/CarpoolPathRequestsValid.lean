import AFTD.Prelude
import AFTD.Kb.Tcs.CarpoolPathRequests
import AFTD.Kb.Tcs.ValidCarpoolEdgeSequence

/-!
# carpool_path_requests_valid

Topic: online_algorithms   Node: 553711ccc21d

Provenance: helper lemma. OP-2130, proposed here; arXiv:2609.21348 Theorem 1.1 gives a deterministic bound for greedy, while arXiv:2611.00388 proves a cubic tail for a different randomized algorithm.

Every path request has distinct endpoints.
-/

theorem carpool_path_requests_valid (n : ℕ) (edges : List (Fin n × Fin n)) (h : carpool_path_requests n edges) : ValidCarpoolEdgeSequence n edges := by
  intro e he heq
  have hindex := h e he
  have hv : e.1.val = e.2.val := congrArg Fin.val heq
  omega
