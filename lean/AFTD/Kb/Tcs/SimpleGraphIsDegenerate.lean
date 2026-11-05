import AFTD.Prelude

/-!
# simple_graph_is_degenerate

Topic: graphs   Node: 16473d6edd85

Provenance: formalization of a published result. Source: arXiv:2611.04674, Section 1

A simple graph G on a vertex type V is k-degenerate if for every nonempty subset of vertices s ⊆ V, there exists a vertex v ∈ s such that the cardinality of the set of neighbors of v lying in s is at most k.
-/

/-- A simple graph is k-degenerate if every nonempty subset of vertices contains a vertex with at most k neighbors in the subset. -/
def simple_graph_is_degenerate {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop := ∀ s : Set V, s.Nonempty → ∃ v ∈ s, (s ∩ G.neighborSet v).encard ≤ k
