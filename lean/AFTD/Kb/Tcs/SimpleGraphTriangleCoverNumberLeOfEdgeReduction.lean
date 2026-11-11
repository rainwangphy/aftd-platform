import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTriangleCoverNumber
import AFTD.Kb.Tcs.FiniteVertexSetEdgeEncoding
import AFTD.Kb.Tcs.F

/-!
# simple_graph_triangle_cover_number_le_of_edge_reduction

Topic: graphs   Node: 8f3a55419ccb

Provenance: helper lemma. arXiv:2611.11128 Lemma 2.2 -- Triangle-overlap cores and density bounds for Tuza's conjecture

Let G be a finite simple graph, F a nonempty edge subset, S a pairwise edge-disjoint triangle family, and X an edge subset such that X meets every triangle containing an edge of F and E(S) \ F ⊆ X. Then the triangle cover number of G is at most that of G \ (F ∪ X) plus |X|.
-/

lemma simple_graph_triangle_cover_number_le_of_edge_reduction_cover_nonempty
    {V : Type*} [Fintype V] (H : SimpleGraph V) :
    {n : ℕ | ∃ F : Finset (Sym2 V), (∀ f ∈ F, f ∈ H.edgeSet) ∧
      (∀ t : Finset V, H.IsNClique 3 t → ∃ f ∈ F, ∀ x ∈ f, x ∈ t) ∧ F.card = n}.Nonempty := by
  classical
  refine ⟨_, H.edgeFinset, ?_, ?_, rfl⟩
  · intro f hf; rwa [SimpleGraph.mem_edgeFinset] at hf
  · intro t ht
    obtain ⟨u, v, w, huv, -, -, rfl⟩ := Finset.card_eq_three.mp ht.card_eq
    refine ⟨s(u, v), ?_, ?_⟩
    · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      exact ht.isClique (by simp) (by simp) huv
    · intro x hx
      rw [Sym2.mem_iff] at hx
      rcases hx with rfl | rfl <;> simp

open Classical in
/-- Under an edge reduction (F, S, X), the triangle cover number of G is at most that of G \ (F ∪ X) plus |X|. -/
theorem simple_graph_triangle_cover_number_le_of_edge_reduction
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (F : Finset (Sym2 V)) (hF : F ⊆ G.edgeFinset) (hFne : F.Nonempty)
    (S : Finset (Finset V)) (hS : ∀ t ∈ S, G.IsNClique 3 t)
    (hSpairwise : (S : Set (Finset V)).Pairwise (fun s t => (s ∩ t).card ≤ 1))
    (X : Finset (Sym2 V)) (hX : X ⊆ G.edgeFinset)
    (hXmeets : ∀ t : Finset V, G.IsNClique 3 t →
      (∃ e ∈ F, ∀ x ∈ e, x ∈ t) → ∃ e ∈ X, ∀ x ∈ e, x ∈ t)
    (hES : (S.biUnion finite_vertex_set_edge_encoding \ F) ⊆ X) :
    simple_graph_triangle_cover_number G ≤
      simple_graph_triangle_cover_number (G.deleteEdges (↑(F ∪ X) : Set (Sym2 V))) + X.card := by
  set H : SimpleGraph V := G.deleteEdges (↑(F ∪ X) : Set (Sym2 V))
  obtain ⟨C, hCsub, hCcov, hCcard⟩ :=
    Nat.sInf_mem (simple_graph_triangle_cover_number_le_of_edge_reduction_cover_nonempty H)
  change C.card = simple_graph_triangle_cover_number H at hCcard
  have hsubG : ∀ e ∈ C ∪ X, e ∈ G.edgeSet := by
    intro e he
    rw [Finset.mem_union] at he
    rcases he with heC | heX
    · have := hCsub e heC
      rw [SimpleGraph.edgeSet_deleteEdges] at this
      exact this.1
    · have := hX heX
      rwa [SimpleGraph.mem_edgeFinset] at this
  have hcovG : ∀ t : Finset V, G.IsNClique 3 t → ∃ e ∈ C ∪ X, ∀ x ∈ e, x ∈ t := by
    intro t ht
    by_cases hclq : H.IsClique (↑t : Set V)
    · obtain ⟨e, heC, het⟩ := hCcov t ⟨hclq, ht.card_eq⟩
      exact ⟨e, Finset.mem_union_left X heC, het⟩
    · rw [SimpleGraph.isClique_iff, Set.Pairwise] at hclq
      push Not at hclq
      obtain ⟨u, hu, v, hv, huv, hnotadj⟩ := hclq
      have hGadj : G.Adj u v := ht.isClique hu hv huv
      rw [SimpleGraph.deleteEdges_adj] at hnotadj
      have hdel : s(u, v) ∈ (↑(F ∪ X) : Set (Sym2 V)) := by
        by_contra h
        exact hnotadj ⟨hGadj, h⟩
      rw [Finset.mem_coe, Finset.mem_union] at hdel
      have hxuv : ∀ x ∈ s(u, v), x ∈ t := by
        intro x hx
        rw [Sym2.mem_iff] at hx
        rcases hx with rfl | rfl <;> assumption
      rcases hdel with hdelF | hdelX
      · obtain ⟨e, heX, het⟩ := hXmeets t ht ⟨s(u, v), hdelF, hxuv⟩
        exact ⟨e, Finset.mem_union_right C heX, het⟩
      · exact ⟨s(u, v), Finset.mem_union_right C hdelX, hxuv⟩
  have hmemG : (C ∪ X).card ∈ {n : ℕ | ∃ F' : Finset (Sym2 V), (∀ e ∈ F', e ∈ G.edgeSet) ∧
      (∀ t : Finset V, G.IsNClique 3 t → ∃ e ∈ F', ∀ x ∈ e, x ∈ t) ∧ F'.card = n} :=
    ⟨C ∪ X, hsubG, hcovG, rfl⟩
  have hle : simple_graph_triangle_cover_number G ≤ (C ∪ X).card := Nat.sInf_le hmemG
  have hcardle : (C ∪ X).card ≤ simple_graph_triangle_cover_number H + X.card := by
    have := Finset.card_union_le C X
    omega
  exact hle.trans hcardle
