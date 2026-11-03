import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraph

/-!
# digraph_two_common_parents_edge_multiplicity

Topic: graphs   Node: 26da2288bf9b

Provenance: helper lemma. Collision-charge construction for the small-overlap route to OP-110.

Two distinct vertices with two distinct common predecessors form an edge in the common-predecessor graph with multiplicity at least two.
-/

private instance in504_common_parents_decAdj {α : Type} [Fintype α] [DecidableEq α] (D : Digraph α)
    [DecidableRel D.Adj] : DecidableRel (digraph_common_predecessor_graph D).Adj := by
  intro u v
  unfold digraph_common_predecessor_graph
  infer_instance

theorem digraph_two_common_parents_edge_multiplicity
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (a b t p : α) (hab : a ≠ b) (htp : t ≠ p)
    (hta : D.Adj t a) (htb : D.Adj t b)
    (hpa : D.Adj p a) (hpb : D.Adj p b) :
    s(a,b) ∈ (digraph_common_predecessor_graph D).edgeFinset ∧
      2 ≤ (Finset.univ.filter fun q => ∀ x, x ∈ s(a,b) → D.Adj q x).card := by
  classical
  constructor
  · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact ⟨hab,t,hta,htb⟩
  · let P : Finset α := Finset.univ.filter fun q => ∀ x, x ∈ s(a,b) → D.Adj q x
    have ht : t ∈ P := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro x hx
      rcases Sym2.mem_iff.mp hx with rfl | rfl
      · exact hta
      · exact htb
    have hp : p ∈ P := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro x hx
      rcases Sym2.mem_iff.mp hx with rfl | rfl
      · exact hpa
      · exact hpb
    have hs : ({t,p} : Finset α) ⊆ P := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact ht
      · exact hp
    have hc := Finset.card_le_card hs
    change 2 ≤ P.card
    have hcard : ({t,p} : Finset α).card = 2 := by simp [htp]
    rw [hcard] at hc
    exact hc
