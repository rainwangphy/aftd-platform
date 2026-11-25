import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# simple_graph_subgraphs_inclusion_exclusion

Topic: graphs   Node: 28df4207813e

Provenance: helper lemma. step towards k_connected_longest_cycles_intersection_bound

For any two subgraphs of a finite graph on n vertices with equal vertex cardinality, the number of vertices in their intersection is at least 2L - n.
-/

/-- For any two subgraphs of a finite graph on n vertices with equal vertex cardinality, the number of vertices in their intersection is at least 2L - n. -/
theorem simple_graph_subgraphs_inclusion_exclusion {V : Type*} [Fintype V] (G : SimpleGraph V) (C D : G.Subgraph) (h_eq : C.verts.ncard = D.verts.ncard) : 2 * (C.verts.ncard : ℤ) - (Fintype.card V : ℤ) ≤ ((C.verts ∩ D.verts).ncard : ℤ) := by
  have hcard : Nat.card V = Fintype.card V := Nat.card_eq_fintype_card
  have hunion_le : (C.verts ∪ D.verts).ncard ≤ Fintype.card V := by
    simpa [hcard] using Set.ncard_le_card (C.verts ∪ D.verts)
  have hIE := Set.ncard_union_add_ncard_inter C.verts D.verts
  have hsum : (C.verts ∪ D.verts).ncard + (C.verts ∩ D.verts).ncard = 2 * C.verts.ncard := by
    rw [hIE, h_eq]
    ring
  have hsumZ : ((C.verts ∪ D.verts).ncard : ℤ) + ((C.verts ∩ D.verts).ncard : ℤ) = 2 * (C.verts.ncard : ℤ) := by
    exact_mod_cast hsum
  have hunionZ : ((C.verts ∪ D.verts).ncard : ℤ) ≤ (Fintype.card V : ℤ) := by
    exact_mod_cast hunion_le
  linarith
