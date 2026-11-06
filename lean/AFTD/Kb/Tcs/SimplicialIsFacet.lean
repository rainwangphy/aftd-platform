import AFTD.Prelude

/-!
# simplicial_is_facet

Topic: combinatorics   Node: f0ac975cc5a5

Provenance: formalization of a published result. Source: arXiv:2611.08071 Section 3

A face F of an abstract simplicial complex Δ is a facet if it is maximal with respect to inclusion among all faces of Δ.
-/

/-- A facet of an abstract simplicial complex is a maximal face under inclusion. -/
def simplicial_is_facet {V : Type*} (Δ : AbstractSimplicialComplex V) (F : Finset V) : Prop := F ∈ Δ.faces ∧ ∀ G ∈ Δ.faces, F ⊆ G → F = G
