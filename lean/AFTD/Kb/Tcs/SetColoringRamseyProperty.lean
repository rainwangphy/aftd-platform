import AFTD.Prelude
import AFTD.Kb.Tcs.SupportGraph

/-!
# set_coloring_ramsey_property

Topic: combinatorics   Node: e6b0895ce728

Provenance: formalization of a published result. Source: scout/2611-15376-set-coloring-ramsey-numbers-with-multiple-intersections.md:147

Given a type V, a simple graph G on V, and natural numbers r, s, t, N, set_coloring_ramsey_property G r s t N asserts that for every edge-coloring ϕ : (⊤ : SimpleGraph (Fin N)).edgeSet → Finset (Fin r) assigning an s-element finite subset of Fin r to each edge of the complete graph on Fin N, there exists a t-element finite subset T : Finset (Fin r) such that the support graph support_graph ϕ T contains a copy of G.
-/

/-- The generalized set-coloring Ramsey property at N. -/
def set_coloring_ramsey_property {V : Type*} (G : SimpleGraph V) (r s t N : ℕ) : Prop :=
  ∀ ϕ : (⊤ : SimpleGraph (Fin N)).edgeSet → Finset (Fin r),
    (∀ e, (ϕ e).card = s) →
    ∃ T : Finset (Fin r), T.card = t ∧ SimpleGraph.IsContained G (support_graph ϕ T)
