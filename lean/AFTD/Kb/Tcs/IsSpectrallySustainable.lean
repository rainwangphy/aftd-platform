import AFTD.Prelude
import AFTD.Kb.Tcs.IsSpectrallySustainableEdge

/-!
# is_spectrally_sustainable

Topic: graphs   Node: 849d08dd17b1

Provenance: formalization of a published result. Source: arXiv:2610.17078, Sustainable trees, Section 1

A simple graph G on a finite vertex set is spectrally sustainable if G is connected and every edge of G is spectrally sustainable.
-/

/-- A simple graph is spectrally sustainable if it is connected and every edge is spectrally sustainable. -/
def is_spectrally_sustainable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : Prop := G.Connected ∧ ∀ e ∈ G.edgeSet, is_spectrally_sustainable_edge G e
