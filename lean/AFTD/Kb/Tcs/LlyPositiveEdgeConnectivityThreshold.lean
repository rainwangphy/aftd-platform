import AFTD.Prelude
import AFTD.Kb.Tcs.GraphEdgeConnectivity
import AFTD.Kb.Tcs.GraphLlyCurvature

/-!
# lly_positive_edge_connectivity_threshold

Topic: graphs   Node: 188ef4378bc0

Provenance: original. Related work: Open-problem entry OP-165 after arXiv:2610.10559 (Edge-Connectivity versus Lin--Lu--Yau Curvature), Theorems 1.3–1.4 (Theorem 1.3 gives c(n) ≤ ⌈2n/3 − 1⌉).

c(n): the smallest natural number k such that every connected simple graph on n vertices with edge-connectivity at least k has positive Lin–Lu–Yau curvature on every edge.
-/

/-- `c(n)`: least `k` such that every connected graph on `n` vertices with edge-connectivity `≥ k` has positive Lin–Lu–Yau curvature on all edges. -/
noncomputable def lly_positive_edge_connectivity_threshold (n : ℕ) : ℕ :=
  sInf {k | ∀ G : SimpleGraph (Fin n), ∀ [DecidableRel G.Adj], G.Connected →
    k ≤ graph_edge_connectivity G → ∀ x y, G.Adj x y → 0 < graph_lly_curvature G x y}
