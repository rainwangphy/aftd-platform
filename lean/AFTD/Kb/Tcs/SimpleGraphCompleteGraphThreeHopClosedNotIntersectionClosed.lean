import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsHopClosed
import AFTD.Kb.Tcs.SimpleGraphIsHop

/-!
# simple_graph_completeGraph_three_hop_closed_not_intersection_closed

Topic: graphs   Node: afff08873e32

Provenance: helper lemma. arXiv:2610.18463 Question 5.9

The collection of hop-closed edge subsets of the complete graph K₃ on 3 vertices is not closed under intersection.
-/

open SimpleGraph

private def simple_graph_completeGraph_three_hop_closed_not_intersection_closed_e01 : Sym2 (Fin 3) := s(0, 1)
private def simple_graph_completeGraph_three_hop_closed_not_intersection_closed_e02 : Sym2 (Fin 3) := s(0, 2)
private def simple_graph_completeGraph_three_hop_closed_not_intersection_closed_e12 : Sym2 (Fin 3) := s(1, 2)

private def simple_graph_completeGraph_three_hop_closed_not_intersection_closed_s1 : Finset (Sym2 (Fin 3)) :=
  {simple_graph_completeGraph_three_hop_closed_not_intersection_closed_e01,
   simple_graph_completeGraph_three_hop_closed_not_intersection_closed_e12}

private def simple_graph_completeGraph_three_hop_closed_not_intersection_closed_s2 : Finset (Sym2 (Fin 3)) :=
  {simple_graph_completeGraph_three_hop_closed_not_intersection_closed_e12,
   simple_graph_completeGraph_three_hop_closed_not_intersection_closed_e02}

private instance (G : SimpleGraph (Fin 3)) [DecidableRel G.Adj] :
    DecidablePred (simple_graph_is_hop G) :=
  fun h => by
    unfold simple_graph_is_hop; infer_instance

private lemma simple_graph_completeGraph_three_hop_closed_not_intersection_closed_edgeSet_top :
    (⊤ : SimpleGraph (Fin 3)).edgeSet =
      {simple_graph_completeGraph_three_hop_closed_not_intersection_closed_e01,
       simple_graph_completeGraph_three_hop_closed_not_intersection_closed_e02,
       simple_graph_completeGraph_three_hop_closed_not_intersection_closed_e12} := by
  ext e
  induction e using Sym2.ind with
  | _ a b =>
    simp only [edgeSet_top, Sym2.mem_diagSet, Sym2.mk_isDiag_iff, Set.mem_compl_iff,
      Set.mem_insert_iff, Set.mem_singleton_iff,
      simple_graph_completeGraph_three_hop_closed_not_intersection_closed_e01,
      simple_graph_completeGraph_three_hop_closed_not_intersection_closed_e02,
      simple_graph_completeGraph_three_hop_closed_not_intersection_closed_e12]
    fin_cases a <;> fin_cases b <;> simp [Sym2.eq_swap]

private lemma simple_graph_completeGraph_three_hop_closed_not_intersection_closed_diff_s1 :
    (⊤ : SimpleGraph (Fin 3)).edgeSet \ (simple_graph_completeGraph_three_hop_closed_not_intersection_closed_s1 : Set (Sym2 (Fin 3))) =
      {simple_graph_completeGraph_three_hop_closed_not_intersection_closed_e02} := by
  rw [simple_graph_completeGraph_three_hop_closed_not_intersection_closed_edgeSet_top]
  ext e
  simp only [simple_graph_completeGraph_three_hop_closed_not_intersection_closed_s1,
    Finset.coe_insert, Finset.coe_singleton, Set.mem_sdiff, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨h1 | h1 | h1, h2⟩
    · exfalso; exact h2 (Or.inl h1)
    · exact h1
    · exfalso; exact h2 (Or.inr h1)
  · rintro rfl
    refine ⟨Or.inr (Or.inl rfl), ?_⟩
    intro h
    rcases h with h | h <;> revert h <;> decide

private lemma simple_graph_completeGraph_three_hop_closed_not_intersection_closed_diff_s2 :
    (⊤ : SimpleGraph (Fin 3)).edgeSet \ (simple_graph_completeGraph_three_hop_closed_not_intersection_closed_s2 : Set (Sym2 (Fin 3))) =
      {simple_graph_completeGraph_three_hop_closed_not_intersection_closed_e01} := by
  rw [simple_graph_completeGraph_three_hop_closed_not_intersection_closed_edgeSet_top]
  ext e
  simp only [simple_graph_completeGraph_three_hop_closed_not_intersection_closed_s2,
    Finset.coe_insert, Finset.coe_singleton, Set.mem_sdiff, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨h1 | h1 | h1, h2⟩
    · exact h1
    · exfalso; exact h2 (Or.inr h1)
    · exfalso; exact h2 (Or.inl h1)
  · rintro rfl
    refine ⟨Or.inl rfl, ?_⟩
    intro h
    rcases h with h | h <;> revert h <;> decide

private lemma simple_graph_completeGraph_three_hop_closed_not_intersection_closed_hop_closed_s1 :
    simple_graph_is_hop_closed (⊤ : SimpleGraph (Fin 3)) (simple_graph_completeGraph_three_hop_closed_not_intersection_closed_s1 : Set (Sym2 (Fin 3))) := by
  unfold simple_graph_is_hop_closed
  refine ⟨?_, ?_⟩
  · rw [simple_graph_completeGraph_three_hop_closed_not_intersection_closed_edgeSet_top]
    intro x hx
    simp only [simple_graph_completeGraph_three_hop_closed_not_intersection_closed_s1,
      Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> simp
  · intro e he
    rw [simple_graph_completeGraph_three_hop_closed_not_intersection_closed_diff_s1, Set.mem_singleton_iff] at he
    subst he
    have h_card1 : Nat.card {h : Equiv.Perm (Fin 3) // simple_graph_is_hop (SimpleGraph.fromEdgeSet (simple_graph_completeGraph_three_hop_closed_not_intersection_closed_s1 : Set (Sym2 (Fin 3)))) h} = 0 := by
      rw [Nat.card_eq_fintype_card]; decide
    have h_card2 : Nat.card {h : Equiv.Perm (Fin 3) // simple_graph_is_hop (SimpleGraph.fromEdgeSet (insert simple_graph_completeGraph_three_hop_closed_not_intersection_closed_e02 (simple_graph_completeGraph_three_hop_closed_not_intersection_closed_s1 : Set (Sym2 (Fin 3))))) h} = 2 := by
      rw [← Finset.coe_insert, Nat.card_eq_fintype_card]; decide
    rw [h_card1, h_card2]
    decide

private lemma simple_graph_completeGraph_three_hop_closed_not_intersection_closed_hop_closed_s2 :
    simple_graph_is_hop_closed (⊤ : SimpleGraph (Fin 3)) (simple_graph_completeGraph_three_hop_closed_not_intersection_closed_s2 : Set (Sym2 (Fin 3))) := by
  unfold simple_graph_is_hop_closed
  refine ⟨?_, ?_⟩
  · rw [simple_graph_completeGraph_three_hop_closed_not_intersection_closed_edgeSet_top]
    intro x hx
    simp only [simple_graph_completeGraph_three_hop_closed_not_intersection_closed_s2,
      Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> simp
  · intro e he
    rw [simple_graph_completeGraph_three_hop_closed_not_intersection_closed_diff_s2, Set.mem_singleton_iff] at he
    subst he
    have h_card1 : Nat.card {h : Equiv.Perm (Fin 3) // simple_graph_is_hop (SimpleGraph.fromEdgeSet (simple_graph_completeGraph_three_hop_closed_not_intersection_closed_s2 : Set (Sym2 (Fin 3)))) h} = 0 := by
      rw [Nat.card_eq_fintype_card]; decide
    have h_card2 : Nat.card {h : Equiv.Perm (Fin 3) // simple_graph_is_hop (SimpleGraph.fromEdgeSet (insert simple_graph_completeGraph_three_hop_closed_not_intersection_closed_e01 (simple_graph_completeGraph_three_hop_closed_not_intersection_closed_s2 : Set (Sym2 (Fin 3))))) h} = 2 := by
      rw [← Finset.coe_insert, Nat.card_eq_fintype_card]; decide
    rw [h_card1, h_card2]
    decide

private lemma simple_graph_completeGraph_three_hop_closed_not_intersection_closed_not_hop_closed_inter :
    ¬ simple_graph_is_hop_closed (⊤ : SimpleGraph (Fin 3))
      ((simple_graph_completeGraph_three_hop_closed_not_intersection_closed_s1 : Set (Sym2 (Fin 3))) ∩
        simple_graph_completeGraph_three_hop_closed_not_intersection_closed_s2) := by
  intro h
  unfold simple_graph_is_hop_closed at h
  rcases h with ⟨-, h2⟩
  have he : simple_graph_completeGraph_three_hop_closed_not_intersection_closed_e01 ∈
      (⊤ : SimpleGraph (Fin 3)).edgeSet \
        ((simple_graph_completeGraph_three_hop_closed_not_intersection_closed_s1 : Set (Sym2 (Fin 3))) ∩
          simple_graph_completeGraph_three_hop_closed_not_intersection_closed_s2) := by
    rw [simple_graph_completeGraph_three_hop_closed_not_intersection_closed_edgeSet_top]
    refine ⟨by simp, ?_⟩
    simp only [simple_graph_completeGraph_three_hop_closed_not_intersection_closed_s1,
      simple_graph_completeGraph_three_hop_closed_not_intersection_closed_s2,
      Finset.coe_insert, Finset.coe_singleton, Set.mem_inter_iff,
      Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro ⟨-, h | h⟩ <;> revert h <;> decide
  specialize h2 simple_graph_completeGraph_three_hop_closed_not_intersection_closed_e01 he
  have h_card1 : Nat.card {h : Equiv.Perm (Fin 3) // simple_graph_is_hop (SimpleGraph.fromEdgeSet
      ((simple_graph_completeGraph_three_hop_closed_not_intersection_closed_s1 : Set (Sym2 (Fin 3))) ∩
        simple_graph_completeGraph_three_hop_closed_not_intersection_closed_s2)) h} = 0 := by
    rw [← Finset.coe_inter, Nat.card_eq_fintype_card]; decide
  have h_card2 : Nat.card {h : Equiv.Perm (Fin 3) // simple_graph_is_hop (SimpleGraph.fromEdgeSet
      (insert simple_graph_completeGraph_three_hop_closed_not_intersection_closed_e01
        ((simple_graph_completeGraph_three_hop_closed_not_intersection_closed_s1 : Set (Sym2 (Fin 3))) ∩
          simple_graph_completeGraph_three_hop_closed_not_intersection_closed_s2))) h} = 0 := by
    rw [← Finset.coe_inter, ← Finset.coe_insert, Nat.card_eq_fintype_card]; decide
  rw [h_card1, h_card2] at h2
  exact Nat.lt_irrefl 0 h2

/-- Hop-closed edge subsets of K₃ are not closed under intersection. -/
theorem simple_graph_completeGraph_three_hop_closed_not_intersection_closed :
    ∃ F₁ F₂ : Set (Sym2 (Fin 3)),
      simple_graph_is_hop_closed (⊤ : SimpleGraph (Fin 3)) F₁ ∧
      simple_graph_is_hop_closed (⊤ : SimpleGraph (Fin 3)) F₂ ∧
      ¬ simple_graph_is_hop_closed (⊤ : SimpleGraph (Fin 3)) (F₁ ∩ F₂) := by
  exact ⟨simple_graph_completeGraph_three_hop_closed_not_intersection_closed_s1,
         simple_graph_completeGraph_three_hop_closed_not_intersection_closed_s2,
         simple_graph_completeGraph_three_hop_closed_not_intersection_closed_hop_closed_s1,
         simple_graph_completeGraph_three_hop_closed_not_intersection_closed_hop_closed_s2,
         simple_graph_completeGraph_three_hop_closed_not_intersection_closed_not_hop_closed_inter⟩
