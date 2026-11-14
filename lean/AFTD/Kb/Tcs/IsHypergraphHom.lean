import AFTD.Prelude

/-!
# is_hypergraph_hom

Topic: combinatorics   Node: e09be0476cf2

Provenance: formalization of a published result. Source: arXiv:2611.16654 Section 2

For types V and W with decidable equality on W, finite hyperedge sets F : Finset (Finset V) and G : Finset (Finset W), and a map f : V → W, is_hypergraph_hom F G f asserts that for every hyperedge e ∈ F, the image finset e.image f belongs to G.
-/

/-- A map between vertex sets is a hypergraph homomorphism if it maps every hyperedge to a hyperedge. -/
def is_hypergraph_hom {V W : Type*} [DecidableEq W]
    (F : Finset (Finset V)) (G : Finset (Finset W)) (f : V → W) : Prop := ∀ e ∈ F, e.image f ∈ G
