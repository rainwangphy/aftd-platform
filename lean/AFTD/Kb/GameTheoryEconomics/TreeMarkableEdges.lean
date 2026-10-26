import AFTD.Prelude

/-!
# tree_markable_edges

Topic: combinatorial_games   Node: 26a7f95e899e

Provenance: formalization of a published result. Source: arXiv:2610.15145, Section 1 and 2

The number of markable edges of a graph is the number of edges not incident to any leaf.
-/

/-- The number of markable edges of a graph: edges where neither endpoint is a leaf. -/
noncomputable def tree_markable_edges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ := (G.edgeFinset.filter (fun e => ∀ v ∈ e, G.degree v ≠ 1)).card
