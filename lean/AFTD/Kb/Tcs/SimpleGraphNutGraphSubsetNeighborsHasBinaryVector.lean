import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsNutGraph

/-!
# simple_graph_nut_graph_subset_neighbors_has_binary_vector

Topic: graphs   Node: dab65c2eca7b

Provenance: original. Related work: arXiv:2611.08244 Thm 4.1

Let G be a finite simple nut graph on a vertex set V of cardinality at least 4. If there exist vertices u and v such that the neighbor set of v is a strict subset of the neighbor set of u, then there exists a non-zero (0,1)-vector in the row space of G.adjMatrix ℝ over ℝ that does not equal any row of G.adjMatrix ℝ.
-/

private lemma simple_graph_nut_graph_subset_neighbors_has_binary_vector_toLin'_adjMatrix_single
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (w : V) :
    Matrix.toLin' (G.adjMatrix ℝ) (Pi.single w (1 : ℝ)) = G.adjMatrix ℝ w := by
  rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]
  funext i
  exact ((SimpleGraph.isSymm_adjMatrix (α := ℝ) (G := G)).apply i w).symm

/-- If a finite simple nut graph on at least 4 vertices has two vertices with strictly nested neighborhoods, it has a non-row binary vector in its adjacency row space. -/
theorem simple_graph_nut_graph_subset_neighbors_has_binary_vector
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hnut : simple_graph_is_nut_graph G)
    (hcard : 4 ≤ Fintype.card V)
    (u v : V) (hsub : G.neighborSet v ⊂ G.neighborSet u) :
    ∃ y : V → ℝ, (∀ w : V, y w = 0 ∨ y w = 1) ∧ y ≠ 0 ∧
      y ∈ LinearMap.range (Matrix.toLin' (G.adjMatrix ℝ)) ∧
      ∀ l : V, y ≠ G.adjMatrix ℝ l := by
  obtain ⟨hnull, hall⟩ := hnut
  refine ⟨G.adjMatrix ℝ u - G.adjMatrix ℝ v, ?_, ?_, ?_, ?_⟩
  · intro w
    have hmem : G.Adj v w → G.Adj u w := fun hvw => hsub.1 hvw
    by_cases hvw : G.Adj v w
    · have huw := hmem hvw
      left
      simp [Pi.sub_apply, SimpleGraph.adjMatrix_apply, huw, hvw]
    · by_cases huw : G.Adj u w
      · right
        simp [Pi.sub_apply, SimpleGraph.adjMatrix_apply, huw, hvw]
      · left
        simp [Pi.sub_apply, SimpleGraph.adjMatrix_apply, huw, hvw]
  · intro hzero
    obtain ⟨w0, hw0u, hw0v⟩ := Set.exists_of_ssubset hsub
    have h := congr_fun hzero w0
    simp only [Pi.sub_apply, Pi.zero_apply, SimpleGraph.adjMatrix_apply] at h
    rw [if_pos (show G.Adj u w0 from hw0u), if_neg (show ¬ G.Adj v w0 from hw0v)] at h
    norm_num at h
  · rw [← simple_graph_nut_graph_subset_neighbors_has_binary_vector_toLin'_adjMatrix_single G u,
        ← simple_graph_nut_graph_subset_neighbors_has_binary_vector_toLin'_adjMatrix_single G v,
        ← LinearMap.map_sub]
    exact LinearMap.mem_range_self _ _
  · intro l heq
    obtain ⟨w0, hw0u, hw0v⟩ := Set.exists_of_ssubset hsub
    have huv : u ≠ v := by
      intro h; subst h; exact hw0v hw0u
    set x : V → ℝ := Pi.single u (1 : ℝ) - Pi.single v (1 : ℝ) - Pi.single l (1 : ℝ) with hxdef
    have hmap : Matrix.toLin' (G.adjMatrix ℝ) x =
        (G.adjMatrix ℝ u - G.adjMatrix ℝ v) - G.adjMatrix ℝ l := by
      simp only [hxdef]
      rw [map_sub, map_sub,
          simple_graph_nut_graph_subset_neighbors_has_binary_vector_toLin'_adjMatrix_single G u,
          simple_graph_nut_graph_subset_neighbors_has_binary_vector_toLin'_adjMatrix_single G v,
          simple_graph_nut_graph_subset_neighbors_has_binary_vector_toLin'_adjMatrix_single G l]
    have hx_ker : x ∈ LinearMap.ker (Matrix.toLin' (G.adjMatrix ℝ)) := by
      rw [LinearMap.mem_ker, hmap, heq, sub_self]
    have hx_ne : x ≠ 0 := by
      intro hzero
      have h := congr_fun hzero v
      simp only [hxdef, Pi.sub_apply, Pi.zero_apply] at h
      rw [Pi.single_eq_of_ne huv.symm, Pi.single_eq_same] at h
      by_cases hlv : l = v
      · rw [hlv, Pi.single_eq_same] at h
        norm_num at h
      · rw [Pi.single_eq_of_ne (Ne.symm hlv)] at h
        norm_num at h
    have hex : ∃ w : V, w ≠ u ∧ w ≠ v ∧ w ≠ l := by
      have hlt : ({u, v, l} : Finset V).card < (Finset.univ : Finset V).card := by
        rw [Finset.card_univ]
        have h3 := Finset.card_le_three (a := u) (b := v) (c := l)
        omega
      obtain ⟨w, _, hw⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      exact ⟨w, (by intro h; exact hw (by simp [h])),
                 (by intro h; exact hw (by simp [h])),
                 (by intro h; exact hw (by simp [h]))⟩
    obtain ⟨w, hwu, hwv, hwl⟩ := hex
    have hwzero : x w = 0 := by
      simp [hxdef, hwu, hwv, hwl]
    exact (hall x hx_ker hx_ne w) hwzero
