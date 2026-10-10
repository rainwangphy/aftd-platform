import AFTD.Prelude

/-!
# graph_edge_connectivity

Topic: graphs   Node: 7985f756db3c

Provenance: formalization of a published result. Source: arXiv:2610.10559 (Edge-Connectivity versus Lin--Lu--Yau Curvature), Sec. 1 (edge-connectivity: the minimum number of edges whose removal disconnects the graph; 0 for a single vertex); expressed through Mathlib's `SimpleGraph.IsEdgeConnected`.

The edge-connectivity κ'(G): the largest k such that removing fewer than k edges never disconnects G (0 for a disconnected graph; 0 also for a single vertex, as in the paper's convention).
-/

/-- Edge-connectivity `κ'(G)`: the largest `k` with `G.IsEdgeConnected k` (Mathlib: deleting fewer than `k` edges keeps every pair reachable). -/
noncomputable def graph_edge_connectivity {V : Type*} (G : SimpleGraph V) : ℕ :=
  sSup {k | G.IsEdgeConnected k}
