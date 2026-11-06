import AFTD.Prelude

/-!
# simplicial_is_minimal_nonface

Topic: combinatorics   Node: b1d3efe70fd2

Provenance: formalization of a published result. Source: arXiv:2611.08071 Section 3

Given an abstract simplicial complex Δ of type AbstractSimplicialComplex V, a finite subset M of V of cardinality at least 2 is a minimal nonface of Δ if M is not in Δ.faces, but every proper nonempty subset of M belongs to Δ.faces.
-/

/-- A minimal nonface of an abstract simplicial complex. -/
def simplicial_is_minimal_nonface {V : Type*} (Δ : AbstractSimplicialComplex V) (M : Finset V) : Prop := 2 ≤ M.card ∧ M ∉ Δ.faces ∧ ∀ T ⊂ M, T.Nonempty → T ∈ Δ.faces
