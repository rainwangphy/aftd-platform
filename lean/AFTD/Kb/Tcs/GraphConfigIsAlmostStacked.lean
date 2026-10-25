import AFTD.Prelude

/-!
# graph_config_is_almost_stacked

Topic: graphs   Node: f56211712141

Provenance: formalization of a published result. Source: arXiv:2610.09650 Def 3.1

A configuration c on a graph is almost stacked if at most one vertex carries more than one pebble, meaning there exists a vertex r such that every other vertex v ≠ r satisfies c(v) ≤ 1.
-/

/-- A pebbling configuration on a graph is almost stacked if at most one vertex carries more than one pebble. -/
def graph_config_is_almost_stacked {V : Type*} (c : V → ℕ) : Prop := ∃ r : V, ∀ v : V, v ≠ r → c v ≤ 1
