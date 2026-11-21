import AFTD.Prelude

/-!
# simple_graph_odd_components_card_le_vertices

Topic: graphs   Node: 150da3126b52

Provenance: helper lemma. OP-1957: bound the barrier size by the cardinality of the extra component part.

A finite graph has at most as many odd connected components as vertices.
-/

theorem simple_graph_odd_components_card_le_vertices
    {V : Type*} [Fintype V] (G : SimpleGraph V) :
    G.oddComponents.ncard ≤ Fintype.card V := by
  classical
  have hsurj : Function.Surjective G.connectedComponentMk := by
    intro c
    obtain ⟨v, hv⟩ := c.nonempty_supp
    exact ⟨v, hv⟩
  have hcomp : Nat.card G.ConnectedComponent ≤ Fintype.card V := by
    simpa only [Nat.card_eq_fintype_card] using
      (Nat.card_le_card_of_surjective G.connectedComponentMk hsurj)
  have hodd : G.oddComponents.ncard ≤ Nat.card G.ConnectedComponent := by
    rw [← Set.ncard_univ]
    exact Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
  exact hodd.trans hcomp
