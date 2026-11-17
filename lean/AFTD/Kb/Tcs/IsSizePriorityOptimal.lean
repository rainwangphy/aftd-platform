import AFTD.Prelude
import AFTD.Kb.Tcs.BipartiteMatchings

/-!
# is_size_priority_optimal

Topic: graphs   Node: 669000dc673e

Provenance: formalization of a published result. Source: arXiv:2601.20502 (Optimal matching under size priority), Section 1: the size-priority optimal matching, minimum cost among maximum-cardinality matchings.

Given the bipartite graph on Fin n + Fin n with edge set E and real edge costs w, a set M of pairs is size-priority optimal when it is a matching of E (bipartite_matchings n E), no matching of E has more edges than M, and every matching of E with as many edges as M has total cost (sum of w over its edges) at least that of M; that is, M minimizes total cost among maximum-cardinality matchings.
-/

def is_size_priority_optimal (n : ℕ) (E : Finset (Fin n × Fin n)) (w : Fin n × Fin n → ℝ)
    (M : Finset (Fin n × Fin n)) : Prop :=
  M ∈ bipartite_matchings n E ∧ (∀ M' ∈ bipartite_matchings n E, M'.card ≤ M.card) ∧
    ∀ M' ∈ bipartite_matchings n E, M'.card = M.card → ∑ e ∈ M, w e ≤ ∑ e ∈ M', w e
