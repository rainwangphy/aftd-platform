import AFTD.Prelude

/-!
# simple_graph_leaf_neighbor_count

Topic: graphs   Node: 6bbc8b39cb29

Provenance: formalization of a published result. Source: arXiv:2610.11446 (On the local average order of dominating sets), Sec. 1 (leaf, stem, l-stem: a stem with l leaf neighbours).

The number of leaf neighbours (neighbours of degree one) of a vertex v; v is an l-stem when this number is l ≥ 1.
-/

/-- The number of leaf neighbours of `v` (neighbours of degree one): `v` is an `l`-stem when this is `l ≥ 1`. -/
def simple_graph_leaf_neighbor_count {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℕ :=
  ((G.neighborFinset v).filter (fun u => G.degree u = 1)).card
