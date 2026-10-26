import AFTD.Prelude

/-!
# is_circulant_graph

Topic: combinatorics   Node: bacb16fb2bfb

Provenance: formalization of a published result. Source: arXiv:2610.31807 Section 8

A simple graph G on N vertices is circulant if it is isomorphic to the Cayley graph of ZMod N with respect to some connection set s.
-/

/-- A simple graph on N vertices is circulant if it is isomorphic to a circulant graph on ZMod N. -/
def is_circulant_graph {V : Type*} (N : ℕ) (G : SimpleGraph V) : Prop := ∃ s : Set (ZMod N), Nonempty (G ≃g SimpleGraph.circulantGraph s)
