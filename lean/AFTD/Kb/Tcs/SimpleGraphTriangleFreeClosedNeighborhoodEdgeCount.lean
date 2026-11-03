import AFTD.Prelude

/-!
# simple_graph_triangle_free_closed_neighborhood_edge_count

Topic: combinatorics   Node: 71eb57401e1f

Provenance: helper lemma. Closed-neighborhood edge accounting for OP-926, https://arxiv.org/abs/2401.00392, Section 2.

In a finite triangle-free graph, the number of edges induced by the vertices outside the closed neighborhood of v plus the sum of the degrees of the neighbors of v equals the total number of edges.
-/

theorem simple_graph_triangle_free_closed_neighborhood_edge_count {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α) [DecidableRel G.Adj] (htri : G.CliqueFree 3) (v : α) :
    (G.induce {u | u ≠ v ∧ ¬ G.Adj v u}).edgeFinset.card +
      (∑ u ∈ G.neighborFinset v, G.degree u) = G.edgeFinset.card := by
  classical
  let S : Set α := {u | u ≠ v ∧ ¬ G.Adj v u}
  have hE₁ : (G.induce S).edgeFinset.card = (G.edgeFinset ∩ S.toFinset.sym2).card := by
    rw [← SimpleGraph.map_edgeFinset_induce (G := G) (s := S), Finset.card_map]
  have hEdges : G.edgeFinset \ S.toFinset.sym2 =
      (G.neighborFinset v).biUnion (fun u => G.incidenceFinset u) := by
    ext e
    induction e using Sym2.ind with
    | h x y =>
      simp only [Finset.mem_sdiff, Finset.mem_biUnion, SimpleGraph.mem_incidenceFinset,
        SimpleGraph.mem_edgeFinset, Finset.mem_sym2_iff,
        Set.mem_toFinset, SimpleGraph.mem_neighborFinset, SimpleGraph.incidenceSet,
        Sym2.mem_iff, Set.mem_ofPred_eq, S, SimpleGraph.mem_edgeSet]
      constructor
      · rintro ⟨hxy, hnot⟩
        push Not at hnot
        obtain ⟨a, ha, hav⟩ := hnot
        rcases ha with hax | hay
        · subst a
          by_cases hxv : x = v
          · subst x
            exact ⟨y, hxy, hxy, Or.inr rfl⟩
          · exact ⟨x, hav hxv, hxy, Or.inl rfl⟩
        · subst a
          by_cases hyv : y = v
          · subst y
            exact ⟨x, (G.adj_comm x v).1 hxy, hxy, Or.inl rfl⟩
          · exact ⟨y, hav hyv, hxy, Or.inr rfl⟩
      · rintro ⟨a, hva, hxy, ha⟩
        refine ⟨hxy, ?_⟩
        intro hall
        exact (hall a ha).2 hva
  have hcardUnion : ((G.neighborFinset v).biUnion (fun u => G.incidenceFinset u)).card =
      ∑ u ∈ G.neighborFinset v, G.degree u := by
    rw [Finset.card_biUnion]
    · apply Finset.sum_congr rfl
      intro u hu
      exact SimpleGraph.card_incidenceFinset_eq_degree G u
    · intro u hu w hw hne
      change Disjoint (G.incidenceFinset u) (G.incidenceFinset w)
      have hInd := (G.isIndepSet_iff).1 (G.isIndepSet_neighborSet_of_triangleFree htri v)
      have hnu : ¬ G.Adj u w :=
        hInd ((G.mem_neighborFinset v u).1 hu) ((G.mem_neighborFinset v w).1 hw) hne
      rw [Finset.disjoint_left]
      intro e heu hew
      exact hnu (G.adj_of_mem_incidenceSet hne ((G.mem_incidenceFinset u e).1 heu)
        ((G.mem_incidenceFinset w e).1 hew))
  have hcard : (G.edgeFinset ∩ S.toFinset.sym2).card +
      (G.edgeFinset \ S.toFinset.sym2).card = G.edgeFinset.card := by
    rw [Finset.card_inter_add_card_sdiff]
  change (G.induce S).edgeFinset.card + (∑ u ∈ G.neighborFinset v, G.degree u) = G.edgeFinset.card
  calc
    (G.induce S).edgeFinset.card + (∑ u ∈ G.neighborFinset v, G.degree u)
        = (G.edgeFinset ∩ S.toFinset.sym2).card +
            ((G.neighborFinset v).biUnion (fun u => G.incidenceFinset u)).card := by
          rw [hE₁, ← hcardUnion]
    _ = (G.edgeFinset ∩ S.toFinset.sym2).card +
            (G.edgeFinset \ S.toFinset.sym2).card := by
          rw [← hEdges]
    _ = G.edgeFinset.card := hcard
