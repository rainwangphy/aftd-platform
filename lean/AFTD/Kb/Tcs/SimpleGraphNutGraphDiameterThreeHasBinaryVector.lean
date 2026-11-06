import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsNutGraph
import AFTD.Kb.Tcs.SimpleGraphAdjRowAddIsBinaryOfDistThree
import AFTD.Kb.Tcs.SimpleGraphAdjRowAddMemRange

/-!
# simple_graph_nut_graph_diameter_three_has_binary_vector

Topic: graphs   Node: 4521a91e2c32

Provenance: formalization of a published result. Source: arXiv:2611.08244 Theorem 4.1

Let G be a finite simple nut graph on a finite vertex set. If the diameter of G is 3, then there exists a non-zero (0,1)-vector in the row space of the adjacency matrix of G over ℝ that does not occur as a row of the adjacency matrix.
-/

lemma simple_graph_nut_graph_diameter_three_has_binary_vector_toLin'_adjMatrix_single
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (w : V) :
    Matrix.toLin' (G.adjMatrix ℝ) (Pi.single w 1) = G.adjMatrix ℝ w := by
  set A : Matrix V V ℝ := G.adjMatrix ℝ
  have hsymm : A.IsSymm := SimpleGraph.isSymm_adjMatrix G
  rw [Matrix.toLin'_apply, Matrix.mulVec_single_one]
  funext i
  exact (hsymm.apply i w).symm

/-- Every finite simple nut graph of diameter 3 has a non-zero (0,1)-vector in its adjacency row space not occurring as a row. -/
theorem simple_graph_nut_graph_diameter_three_has_binary_vector
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hnut : simple_graph_is_nut_graph G) (hdiam : G.diam = 3) :
    ∃ y : V → ℝ, (∀ v : V, y v = 0 ∨ y v = 1) ∧ y ≠ 0 ∧
      y ∈ LinearMap.range (Matrix.toLin' (G.adjMatrix ℝ)) ∧
      ∀ u : V, y ≠ G.adjMatrix ℝ u := by
  have : Nontrivial V := SimpleGraph.nontrivial_of_diam_ne_zero (by rw [hdiam]; decide)
  obtain ⟨u, v, hdist⟩ : ∃ u v : V, G.dist u v = 3 := by
    obtain ⟨u, v, huv⟩ := SimpleGraph.exists_dist_eq_diam (G := G)
    rw [hdiam] at huv
    exact ⟨u, v, huv⟩
  have hne : G.dist u v ≠ 0 := by omega
  have hr : G.Reachable u v := SimpleGraph.Reachable.of_dist_ne_zero hne
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  rw [hdist] at hp
  rcases p with _ | ⟨hadj1, _ | ⟨hadj2, _ | ⟨hadj3, _ | _⟩⟩⟩
  · simp at hp
  · simp at hp
  · simp at hp
  · rename_i w1 w2
    refine ⟨G.adjMatrix ℝ u + G.adjMatrix ℝ v, ?_, ?_, ?_, ?_⟩
    · intro w
      exact simple_graph_adj_row_add_is_binary_of_dist_three G u v hdist w
    · intro hzero
      have hw := congr_fun hzero w1
      simp only [Pi.add_apply, Pi.zero_apply, SimpleGraph.adjMatrix_apply] at hw
      rw [if_pos hadj1] at hw
      split_ifs at hw <;> linarith
    · exact simple_graph_adj_row_add_mem_range G u v
    · intro l heq
      have huv : u ≠ v := by
        intro h
        subst h
        simp at hdist
      have hw1u : w1 ≠ u := hadj1.ne.symm
      have hw1v : w1 ≠ v := by
        intro h
        subst h
        have hle := G.dist_le hadj1.toWalk
        simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil, zero_add] at hle
        omega
      have hw2u : w2 ≠ u := by
        intro h
        subst h
        have hle := G.dist_le hadj3.toWalk
        simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_nil, zero_add] at hle
        omega
      have hw2v : w2 ≠ v := hadj3.ne
      have hw1w2 : w1 ≠ w2 := hadj2.ne
      set x : V → ℝ := Pi.single u 1 + Pi.single v 1 - Pi.single l 1
      have hx_ker : x ∈ LinearMap.ker (Matrix.toLin' (G.adjMatrix ℝ)) := by
        rw [LinearMap.mem_ker, map_sub, map_add]
        rw [simple_graph_nut_graph_diameter_three_has_binary_vector_toLin'_adjMatrix_single G u,
            simple_graph_nut_graph_diameter_three_has_binary_vector_toLin'_adjMatrix_single G v,
            simple_graph_nut_graph_diameter_three_has_binary_vector_toLin'_adjMatrix_single G l]
        rw [heq, sub_self]
      have hx_ne : x ≠ 0 := by
        intro hzero
        by_cases hlu : l = u
        · have hv := congr_fun hzero v
          subst hlu
          simp [x] at hv
        · have hu := congr_fun hzero u
          simp [x, hlu, huv] at hu
      have hnut_nz := hnut.2 x hx_ker hx_ne
      by_cases hlw1 : l = w1
      · have hkw2 : x w2 = 0 := by
          have : w2 ≠ l := by subst hlw1; exact hw1w2.symm
          simp [x, hw2u, hw2v, this]
        exact hnut_nz w2 hkw2
      · have hkw1 : x w1 = 0 := by
          simp [x, hw1u, hw1v, hlw1]
        exact hnut_nz w1 hkw1
  · simp at hp
