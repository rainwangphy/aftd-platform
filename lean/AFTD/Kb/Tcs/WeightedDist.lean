import AFTD.Prelude

/-!
# weighted_dist

Topic: graphs   Node: b56005fcae1e

Provenance: formalization of a published result. Source: arXiv:2611.14755, Section 2

The shortest-path distance between vertices u and v in an edge-weighted simple graph (G, w) is the infimum over all walks from u to v of the sum of weights of the edges traversed by the walk.
-/

/-- The shortest-path distance between vertices u and v in a graph G with edge weights w, defined as the infimum of walk lengths between u and v. -/
noncomputable def weighted_dist {V : Type*} (G : SimpleGraph V) (w : Sym2 V → ℝ) (u v : V) : ℝ :=
  sInf (Set.range fun (p : G.Walk u v) => (p.edges.map w).sum)
