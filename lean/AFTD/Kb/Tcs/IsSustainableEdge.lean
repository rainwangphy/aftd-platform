import AFTD.Prelude
import AFTD.Kb.Tcs.AdjacencySpectralRadius

/-!
# is_sustainable_edge

Topic: graphs   Node: 8cd36ef33351

Provenance: formalization of a published result. Source: arXiv:2610.17078 Section 1

An edge e in a tree T is sustainable if there exists a non-edge f such that T - e + f is a tree and the adjacency spectral radius of T - e + f is at least that of T.
-/

/-- An edge e in a tree T is sustainable if replacing it by some non-edge f yields a tree with spectral radius at least that of T. -/
def is_sustainable_edge {V : Type*} [Fintype V] [DecidableEq V] (T : SimpleGraph V) (e : Sym2 V) : Prop := e ∈ T.edgeSet ∧ ∃ f ∈ Tᶜ.edgeSet,
    (T.deleteEdges {e} ⊔ SimpleGraph.fromEdgeSet {f}).IsTree ∧
    adjacency_spectral_radius T ≤ adjacency_spectral_radius (T.deleteEdges {e} ⊔ SimpleGraph.fromEdgeSet {f})
