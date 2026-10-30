import AFTD.Prelude

/-!
# edge_list_connected_cubic

Topic: np_completeness   Node: b529c58f78a9

Provenance: formalization of a published result. Source: arXiv:2610.35794 (Computational complexity of the H-coloring problem in cubic graphs), Sec. 1: the inputs of H-coloring are connected cubic graphs, finite, without loops, possibly with parallel edges; encoded here as an edge list on the vertices 0..n-1

Takes n : ℕ and an edge list es : List (ℕ × ℕ), read as a multigraph on the vertices v < n whose edges are the indices i : Fin es.length, edge i joining es[i].1 and es[i].2 (parallel edges allowed). It holds iff the conjunction of: (1) for every i : Fin es.length, es[i].1 < n ∧ es[i].2 < n ∧ es[i].1 ≠ es[i].2 (no loops); (2) for every v : ℕ with v < n, the Finset of i : Fin es.length with es[i].1 = v ∨ es[i].2 = v has card 3 (the multigraph is cubic); (3) the simple graph SimpleGraph.fromRel on Fin n relating u and v when some i : Fin es.length has es[i].1 = u.val ∧ es[i].2 = v.val is Connected.
-/

/-- A loopless multigraph on vertices v < n, given as an edge list, is cubic and connected. -/
def edge_list_connected_cubic (n : ℕ) (es : List (ℕ × ℕ)) : Prop :=
  (∀ i : Fin es.length, es[i].1 < n ∧ es[i].2 < n ∧ es[i].1 ≠ es[i].2) ∧
  (∀ v : ℕ, v < n → (Finset.univ.filter (fun i : Fin es.length => es[i].1 = v ∨ es[i].2 = v)).card = 3) ∧
  (SimpleGraph.fromRel (fun u v : Fin n => ∃ i : Fin es.length, es[i].1 = u.val ∧ es[i].2 = v.val)).Connected
