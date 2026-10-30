import AFTD.Prelude

/-!
# weighted_graph_dist

Topic: algorithms   Node: eb4b6d470253

Provenance: formalization of a published result. Source: folklore

Given a graph H on vertex type W and edge weights w : Sym2 W → ℝ, the shortest-path distance between u and v is the infimum of edge weight sums over all walks from u to v.
-/

/-- The shortest-path distance between vertices u and v in a graph H with edge weight function w. -/
noncomputable def weighted_graph_dist {W : Type*} (H : SimpleGraph W) (w : Sym2 W → ℝ) (u v : W) : ℝ := ⨅ p : H.Walk u v, (p.edges.map w).sum
