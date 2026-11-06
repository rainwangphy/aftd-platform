import AFTD.Prelude
import AFTD.Kb.Tcs.SimplicialIsFacet

/-!
# simplicial_is_pure

Topic: combinatorics   Node: 726f0000851f

Provenance: formalization of a published result. Source: arXiv:2611.08071 Section 3

An abstract simplicial complex Δ is pure of facet size d if every facet of Δ has cardinality d.
-/

/-- An abstract simplicial complex is pure of facet size d if every facet has cardinality d. -/
def simplicial_is_pure {V : Type*} (Δ : AbstractSimplicialComplex V) (d : ℕ) : Prop := ∀ (F : Finset V), simplicial_is_facet Δ F → F.card = d
