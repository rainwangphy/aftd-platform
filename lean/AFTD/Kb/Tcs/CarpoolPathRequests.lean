import AFTD.Prelude

/-!
# carpool_path_requests

Topic: online_algorithms   Node: 160d424d4521

Provenance: helper lemma. OP-2130, proposed here; arXiv:2609.21348 Theorem 1.1 gives a deterministic bound for greedy, while arXiv:2611.00388 proves a cubic tail for a different randomized algorithm.

Every requested ordered pair joins consecutive vertices of the n-vertex path; repetitions and either endpoint order are allowed.
-/

def carpool_path_requests (n : ℕ) (edges : List (Fin n × Fin n)) : Prop := ∀ e ∈ edges, e.1.val + 1 = e.2.val ∨ e.2.val + 1 = e.1.val
