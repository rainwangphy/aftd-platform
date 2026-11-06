import AFTD.Prelude
import AFTD.Kb.Tcs.SimplicialDualGraph
import AFTD.Kb.Tcs.SimplicialIsFacet

/-!
# simplicial_is_normal

Topic: combinatorics   Node: 3e32c3c0ed73

Provenance: formalization of a published result. Source: arXiv:2611.08071 Section 1

An abstract simplicial complex Δ pure of facet size d is normal if for every face σ of Δ, the subgraph of the dual graph induced by all facets containing σ is connected.
-/

/-- An abstract simplicial complex is normal if the star of every face has a connected dual graph. -/
def simplicial_is_normal {V : Type*} [DecidableEq V] (Δ : AbstractSimplicialComplex V) (d : ℕ) : Prop := ∀ σ ∈ Δ.faces, ((simplicial_dual_graph Δ d).induce {F | σ ⊆ F.1}).Connected
