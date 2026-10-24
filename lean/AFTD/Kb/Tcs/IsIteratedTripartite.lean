import AFTD.Prelude
import AFTD.Kb.Tcs.IsIteratedThreeEdge

/-!
# is_iterated_tripartite

Topic: combinatorics   Node: 57729246ba21

Provenance: formalization of a published result. Source: arXiv:2610.14829 Section 2.2

A hypergraph F is iterated tripartite if there exist a dimension d and a vertex coloring χ : V → (Fin d → Fin 3) that is injective on the vertices incident to edges of F (the union of all edges in F) such that for every hyperedge e in F, the image of e under χ is an edge of the d-iterated blow-up of a single 3-edge (is_iterated_three_edge d (e.image χ)).
-/

/-- A hypergraph F is iterated tripartite if it embeds as a subgraph into an iterated blow-up of a single 3-edge. -/
def is_iterated_tripartite {V : Type*} [DecidableEq V] (F : Finset (Finset V)) : Prop :=
  ∃ (d : ℕ) (χ : V → (Fin d → Fin 3)),
    (∀ u ∈ F.biUnion id, ∀ v ∈ F.biUnion id, χ u = χ v → u = v) ∧
    ∀ e ∈ F, is_iterated_three_edge d (e.image χ)
