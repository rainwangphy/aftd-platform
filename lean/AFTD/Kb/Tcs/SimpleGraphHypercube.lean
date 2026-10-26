import AFTD.Prelude

/-!
# simple_graph_hypercube

Topic: graphs   Node: 6427cf599f13

Provenance: formalization of a published result. Source: arXiv:2610.18463 Question 5.4

The hypercube graph Q_n on vertex set Fin n → Bool, where two vertices are adjacent if and only if they differ at exactly one coordinate.
-/

/-- The hypercube graph Q_n on vertices Fin n → Bool. -/
def simple_graph_hypercube (n : ℕ) : SimpleGraph (Fin n → Bool) :=
  SimpleGraph.fromRel (fun u v => ∃! i : Fin n, u i ≠ v i)
