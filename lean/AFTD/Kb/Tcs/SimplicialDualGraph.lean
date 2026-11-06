import AFTD.Prelude
import AFTD.Kb.Tcs.SimplicialIsFacet

/-!
# simplicial_dual_graph

Topic: combinatorics   Node: b04e45244fa8

Provenance: formalization of a published result. Source: arXiv:2611.08071 Section 3

The dual graph of an abstract simplicial complex pure of facet size d is the simple graph whose vertices are the facets of Δ, where two distinct facets are adjacent if and only if their intersection has cardinality d - 1.
-/

/-- The dual graph of an abstract simplicial complex pure of facet size d. -/
def simplicial_dual_graph {V : Type*} [DecidableEq V] (Δ : AbstractSimplicialComplex V) (d : ℕ) : SimpleGraph {F : Finset V // simplicial_is_facet Δ F} where
  Adj F₁ F₂ := F₁.1 ≠ F₂.1 ∧ (F₁.1 ∩ F₂.1).card = d - 1
  symm := ⟨fun {F₁ F₂} h => ⟨h.1.symm, by rw [Finset.inter_comm, h.2]⟩⟩
  loopless := ⟨fun F h => h.1 rfl⟩
