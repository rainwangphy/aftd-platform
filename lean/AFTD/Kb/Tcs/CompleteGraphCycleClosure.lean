import AFTD.Prelude

/-!
# complete_graph_cycle_closure

Topic: graphs   Node: 879ee2812b27

Provenance: formalization of a published result. Source: arXiv:2611.15741 Section 4 (cycle matroid M(K_n); closure = edges whose endpoints are connected by F)

The closure operator of the cycle matroid M(K_n), as a map on sets of edges of K_n. The ground set is the edge set of the complete graph on Fin n, taken as its own type (elements of (⊤ : SimpleGraph (Fin n)).edgeSet, i.e. unordered pairs s(a,b) with a ≠ b, packaged as a subtype); F is a set of such edges and the closure is again a set of such edges. An edge e of K_n lies in the closure of F iff e = s(a,b) for vertices a, b that are reachable from each other in the simple graph on Fin n whose edge set is (the underlying pairs of) F.
-/

/-- Closure in the cycle matroid of `K_n`: edges whose endpoints are connected by `F`. -/
def complete_graph_cycle_closure (n : ℕ) (F : Set (⊤ : SimpleGraph (Fin n)).edgeSet) :
    Set (⊤ : SimpleGraph (Fin n)).edgeSet :=
  {e | ∃ a b : Fin n, e.val = s(a, b) ∧
    (SimpleGraph.fromEdgeSet (Subtype.val '' F)).Reachable a b}
