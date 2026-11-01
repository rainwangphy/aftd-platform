import AFTD.Prelude

/-!
# ramsey_254_regular_compl_codegree_eq_codegree

Topic: combinatorics   Node: 170c2ea192a5

Provenance: helper lemma. step towards ramsey_b63_b64_seidel_graph_exists

In a 126-regular simple graph G on 254 vertices, a pair of distinct non-adjacent vertices u and v has exactly as many common neighbours in the complement Gᶜ as in G.
-/

/-- For a 126-regular graph on 254 vertices, non-adjacent pairs have equal codegree in G and in Gᶜ. -/
theorem ramsey_254_regular_compl_codegree_eq_codegree
    (G : SimpleGraph (Fin 254)) [DecidableRel G.Adj]
    (hreg : ∀ i : Fin 254, Fintype.card (G.neighborSet i) = 126)
    (u v : Fin 254) (hne : u ≠ v) (hna : ¬ G.Adj u v) :
    Fintype.card (Gᶜ.commonNeighbors u v) = Fintype.card (G.commonNeighbors u v) := by
  classical
  let A : Finset (Fin 254) := Finset.univ.filter (fun w => G.Adj u w)
  let B : Finset (Fin 254) := Finset.univ.filter (fun w => G.Adj v w)
  have hA : A.card = 126 := by
    have h : A = (G.neighborSet u).toFinset := by
      ext w; simp [A, SimpleGraph.mem_neighborSet]
    rw [h, Set.toFinset_card, hreg u]
  have hB : B.card = 126 := by
    have h : B = (G.neighborSet v).toFinset := by
      ext w; simp [B, SimpleGraph.mem_neighborSet]
    rw [h, Set.toFinset_card, hreg v]
  have hAB : A ∩ B = (G.commonNeighbors u v).toFinset := by
    ext w; simp [A, B, SimpleGraph.mem_commonNeighbors]
  have hABint : (A ∩ B).card = Fintype.card (G.commonNeighbors u v) := by
    rw [hAB, Set.toFinset_card]
  have hunion : (A ∪ B).card + (A ∩ B).card = 252 := by
    rw [Finset.card_union_add_card_inter, hA, hB]
  have hcomp : (Gᶜ.commonNeighbors u v).toFinset = (Finset.univ \ (A ∪ B)) \ {u, v} := by
    ext w
    simp only [A, B, Set.mem_toFinset, SimpleGraph.mem_commonNeighbors, SimpleGraph.compl_adj,
      Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, Finset.mem_filter,
      Finset.mem_insert, Finset.mem_singleton, true_and, not_or]
    tauto
  have hsub : ({u, v} : Finset (Fin 254)) ⊆ Finset.univ \ (A ∪ B) := by
    show ({u, v} : Finset (Fin 254)) ⊆
      Finset.univ \ (Finset.univ.filter (fun w => G.Adj u w) ∪ Finset.univ.filter (fun w => G.Adj v w))
    intro w hw
    simp only [Finset.mem_singleton, Finset.mem_insert] at hw
    rcases hw with rfl | rfl
    · simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and]
      rintro (h | h)
      · exact G.irrefl h
      · exact hna h.symm
    · simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and]
      rintro (h | h)
      · exact hna h
      · exact G.irrefl h
  have hcard_uv : ({u, v} : Finset (Fin 254)).card = 2 := Finset.card_pair hne
  have hdiff : ((Finset.univ \ (A ∪ B)) \ {u, v}).card + 2 = (Finset.univ \ (A ∪ B)).card := by
    have h := Finset.card_sdiff_add_card_eq_card hsub
    rw [hcard_uv] at h
    exact h
  have hcompl : (Finset.univ \ (A ∪ B)).card + (A ∪ B).card = 254 := by
    have := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (A ∪ B))
    simpa using this
  have hL : Fintype.card (Gᶜ.commonNeighbors u v) = ((Finset.univ \ (A ∪ B)) \ {u, v}).card := by
    rw [← Set.toFinset_card, hcomp]
  have hR : Fintype.card (G.commonNeighbors u v) = (A ∩ B).card := hABint.symm
  rw [hL, hR]
  omega
