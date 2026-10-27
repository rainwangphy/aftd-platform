import AFTD.Prelude
import AFTD.Kb.Tcs.AdjacencySpectralRadius

/-!
# is_spectrally_sustainable_edge

Topic: graphs   Node: 3b8517e5ff38

Provenance: formalization of a published result. Source: arXiv:2610.17078, Sustainable trees, Section 1

An edge e in a simple graph G on a finite vertex set is spectrally sustainable if there exists a non-edge f of G such that deleting e and adding f yields a connected graph whose adjacency spectral radius is at least that of G.
-/

/-- An edge e in a simple graph G is spectrally sustainable if there is a non-edge f such that G - e + f is connected and its spectral radius is at least that of G. -/
def is_spectrally_sustainable_edge {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (e : Sym2 V) : Prop := e ∈ G.edgeSet ∧ ∃ f ∈ Gᶜ.edgeSet,
    (G.deleteEdges {e} ⊔ SimpleGraph.fromEdgeSet {f}).Connected ∧
    adjacency_spectral_radius G ≤ adjacency_spectral_radius (G.deleteEdges {e} ⊔ SimpleGraph.fromEdgeSet {f})
