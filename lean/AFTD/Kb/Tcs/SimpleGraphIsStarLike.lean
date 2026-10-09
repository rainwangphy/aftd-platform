import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphLeafNeighborCount

/-!
# simple_graph_is_star_like

Topic: graphs   Node: 62aa6a620014

Provenance: formalization of a published result. Source: arXiv:2610.11446 (On the local average order of dominating sets), Lemma 5.1 (star-like graphs: every vertex is a leaf or an l-stem with l ≤ 2).

G is star-like: every vertex is either a leaf (degree one) or an l-stem with 1 ≤ l ≤ 2.
-/

/-- `G` is star-like: every vertex is a leaf (degree one) or an `l`-stem with `1 ≤ l ≤ 2`. -/
def simple_graph_is_star_like {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∀ w, G.degree w = 1 ∨ (1 ≤ simple_graph_leaf_neighbor_count G w ∧
    simple_graph_leaf_neighbor_count G w ≤ 2)
