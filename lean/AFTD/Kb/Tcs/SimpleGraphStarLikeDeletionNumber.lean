import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsStarLike

/-!
# simple_graph_star_like_deletion_number

Topic: graphs   Node: 1ba5da3c1f12

Provenance: original. Related work: arXiv:2208.10475v2: The average size of a dominating set in a graph

The star-like deletion number d_*(G) of a finite simple graph G is the minimum cardinality of a subset X of vertices such that the induced subgraph G - X is star-like.
-/

/-- The minimum number of vertices whose deletion from G leaves an induced star-like subgraph. -/
noncomputable def simple_graph_star_like_deletion_number {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  open scoped Classical in
  sInf {k : ℕ | ∃ X : Finset V, simple_graph_is_star_like (G.induce (Xᶜ : Set V)) ∧ X.card = k}
