import AFTD.Prelude

/-!
# incident_edge_multiset

Topic: combinatorics   Node: 4b404f29f6b5

Provenance: formalization of a published result. Source: arXiv:2611.15376 Sec. 4

Given an edge-coloring ϕ of the complete graph on a finite type V assigning a finite subset of Fin r to each edge, incident_edge_multiset ϕ v is the multiset of edge colors on edges incident to v.
-/

/-- The multiset of edge labels incident to a vertex v in an edge-coloring of the complete graph. -/
def incident_edge_multiset {V : Type*} [Fintype V] [DecidableEq V] {r : ℕ}
    (ϕ : (⊤ : SimpleGraph V).edgeSet → Finset (Fin r)) (v : V) : Multiset (Finset (Fin r)) :=
  ((Finset.univ.erase v).attach.val.map (fun ⟨u, hu⟩ =>
    ϕ ⟨s(u, v), by
      rw [SimpleGraph.mem_edgeSet, SimpleGraph.top_adj]
      exact (Finset.mem_erase.mp hu).1⟩))
