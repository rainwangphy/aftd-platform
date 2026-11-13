import AFTD.Prelude

/-!
# support_graph

Topic: combinatorics   Node: 7ec4af4c8922

Provenance: formalization of a published result. Source: scout/2611-15376-set-coloring-ramsey-numbers-with-multiple-intersections.md:510

Given a type V, a natural number r, an edge-labeling function ϕ : (⊤ : SimpleGraph V).edgeSet → Finset (Fin r) assigning a finite subset Finset (Fin r) to each edge of the complete graph on V, and a target finite subset T : Finset (Fin r), support_graph ϕ T is the SimpleGraph on V whose edges are those edges e of the complete graph on V for which T ⊆ ϕ e.
-/

/-- The support graph H_T of an edge set-coloring ϕ with respect to a subset T of colors. -/
def support_graph {V : Type*} {r : ℕ} (ϕ : (⊤ : SimpleGraph V).edgeSet → Finset (Fin r))
    (T : Finset (Fin r)) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet {e | ∃ h : e ∈ (⊤ : SimpleGraph V).edgeSet, T ⊆ ϕ ⟨e, h⟩}
