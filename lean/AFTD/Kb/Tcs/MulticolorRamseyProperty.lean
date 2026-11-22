import AFTD.Prelude
import AFTD.Kb.Tcs.MonoColorSubgraph

/-!
# multicolor_ramsey_property

Topic: combinatorics   Node: abf90521c6c2

Provenance: formalization of a published result. Source: arXiv:2611.19312 Section 1

For a simple graph H on vertex type V and natural numbers r and N, multicolor_ramsey_property H r N asserts that every r-edge-coloring of the complete graph on Fin N contains a monochromatic copy of H.
-/

/-- Multicolor Ramsey property: every r-edge-coloring of K_N contains a monochromatic copy of H. -/
def multicolor_ramsey_property {V : Type*} (H : SimpleGraph V) (r N : ℕ) : Prop :=
  ∀ c : (⊤ : SimpleGraph (Fin N)).edgeSet → Fin r,
    ∃ col : Fin r, SimpleGraph.IsContained H (mono_color_subgraph ⊤ c col)
