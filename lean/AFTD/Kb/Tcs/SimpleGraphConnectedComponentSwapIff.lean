import AFTD.Prelude

/-!
# simple_graph_connected_component_swap_iff

Topic: communication   Node: bb8c511b62bc

Provenance: helper lemma. arXiv:2611.06626 Claim 2.5

Let G be a simple graph on V. If S ⊆ V contains exactly one representative from each connected component of G, then for any u ∈ S and any v ∈ V, the swapped set (S \ {u}) ∪ {v} intersects every connected component of G if and only if u and v belong to the same connected component (that is, G.Reachable u v).
-/

/-- Swapping a vertex in a transversal of connected components preserves hitting all components iff the vertices are in the same component. -/
theorem simple_graph_connected_component_swap_iff {V : Type*} (G : SimpleGraph V) (S : Set V)
    (hS : ∀ c : G.ConnectedComponent, ∃! x, x ∈ S ∧ G.connectedComponentMk x = c)
    (u : V) (hu : u ∈ S) (v : V) :
    (∀ c : G.ConnectedComponent, ∃ w ∈ (S \ {u}) ∪ {v}, G.connectedComponentMk w = c) ↔
      G.Reachable u v := by
  constructor
  · intro h
    obtain ⟨w, hw, hw_eq⟩ := h (G.connectedComponentMk u)
    rcases hw with hw | hw
    · exfalso
      have hu_uniq := ExistsUnique.unique (hS (G.connectedComponentMk u)) ⟨hw.1, hw_eq⟩ ⟨hu, rfl⟩
      exact hw.2 hu_uniq
    · have hw_v : w = v := Set.mem_singleton_iff.mp hw
      rw [hw_v] at hw_eq
      exact SimpleGraph.ConnectedComponent.eq.mp hw_eq.symm
  · intro h c
    by_cases hc : c = G.connectedComponentMk u
    · subst hc
      refine ⟨v, Set.mem_union_right _ (Set.mem_singleton v), ?_⟩
      exact SimpleGraph.ConnectedComponent.eq.mpr h.symm
    · obtain ⟨x, ⟨hxS, hxc⟩, -⟩ := hS c
      refine ⟨x, Set.mem_union_left _ ⟨hxS, ?_⟩, hxc⟩
      rintro rfl
      exact hc hxc.symm
