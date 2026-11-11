import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTriangleEdgeFamily
import AFTD.Kb.Tcs.FiniteVertexFamilyEdgePackingCoverBridge
import AFTD.Kb.Tcs.SimpleGraphTriangleEdgeFamilyMem
import AFTD.Kb.Tcs.V

/-!
# simple_graph_seven_packing_local_minimum_seed_supergraph_rigidity

Topic: graphs   Node: c85fff825076

Provenance: helper lemma. Finite seed rigidity for the local-exchange obstruction, experiments 17062–17064.

A graph on the nine vertices of the local-exchange seed that contains all seed edges and has triangle packing number at most seven adds no edge other than possibly 07.
-/

open scoped Sym2

private def simple_graph_seven_packing_local_minimum_seed_supergraph_rigidity_edges : Finset (Sym2 (Fin 9)) :=
  {s(0,1), s(0,2), s(0,3), s(0,5), s(1,2), s(1,3), s(1,4), s(1,5), s(1,6), s(1,7),
   s(2,3), s(2,4), s(2,5), s(2,6), s(2,8), s(3,4), s(3,5), s(3,6), s(3,7), s(3,8),
   s(4,5), s(4,6), s(5,6), s(5,7), s(6,7), s(6,8)}

private lemma simple_graph_seven_packing_local_minimum_seed_supergraph_rigidity_adj_of_mem
    {G : SimpleGraph (Fin 9)}
    (hsub : (↑simple_graph_seven_packing_local_minimum_seed_supergraph_rigidity_edges : Set (Sym2 (Fin 9))) ⊆ G.edgeSet)
    {e : Sym2 (Fin 9)} (he : e ∈ G.edgeSet)
    {a b : Fin 9} (h : s(a,b) ∈ simple_graph_seven_packing_local_minimum_seed_supergraph_rigidity_edges ∨ s(a,b) = e) : G.Adj a b := by
  rcases h with h | h
  · rw [← SimpleGraph.mem_edgeSet]; exact hsub h
  · rw [← SimpleGraph.mem_edgeSet, h]; exact he

private lemma simple_graph_seven_packing_local_minimum_seed_supergraph_rigidity_packing_contra
    (G : SimpleGraph (Fin 9))
    (hsub : (↑simple_graph_seven_packing_local_minimum_seed_supergraph_rigidity_edges : Set (Sym2 (Fin 9))) ⊆ G.edgeSet)
    (hle : ∀ P : Finset (Finset (Sym2 (Fin 9))), P ⊆ simple_graph_triangle_edge_family G →
        (P : Set (Finset (Sym2 (Fin 9)))).Pairwise Disjoint → P.card ≤ 7)
    (e : Sym2 (Fin 9)) (he : e ∈ G.edgeSet)
    (x : Finset (Finset (Fin 9))) (hxcard : x.card = 8)
    (hxtri : ∀ t ∈ x, t.card = 3 ∧ ∀ a ∈ t, ∀ b ∈ t, a ≠ b →
      s(a,b) ∈ simple_graph_seven_packing_local_minimum_seed_supergraph_rigidity_edges ∨ s(a,b) = e)
    (hxdisj : (x : Set (Finset (Fin 9))).Pairwise (fun s t => (s ∩ t).card ≤ 1)) :
    False := by
  have hsize : ∀ t ∈ x, 2 ≤ t.card := by
    intro t ht; have := (hxtri t ht).1; omega
  obtain ⟨hcard_eq, hdisj_iff, -⟩ :=
    finite_vertex_family_edge_packing_cover_bridge (V := Fin 9) x (∅ : Finset (Sym2 (Fin 9))) hsize (by simp)
  have hPsub : x.image finite_vertex_set_edge_encoding ⊆ simple_graph_triangle_edge_family G := by
    intro t' ht'
    rw [Finset.mem_image] at ht'
    obtain ⟨t, ht, rfl⟩ := ht'
    rw [simple_graph_triangle_edge_family_mem]
    exact ⟨t, ⟨fun a ha b hb hab =>
        simple_graph_seven_packing_local_minimum_seed_supergraph_rigidity_adj_of_mem hsub he
          ((hxtri t ht).2 a ha b hb hab), (hxtri t ht).1⟩, rfl⟩
  have hPdisj : (x.image finite_vertex_set_edge_encoding : Set (Finset (Sym2 (Fin 9)))).Pairwise Disjoint :=
    hdisj_iff.mpr hxdisj
  have h7 := hle _ hPsub hPdisj
  rw [hcard_eq, hxcard] at h7
  omega

private lemma simple_graph_seven_packing_local_minimum_seed_supergraph_rigidity_cases (e : Sym2 (Fin 9)) :
    ¬ e.IsDiag → e ∉ simple_graph_seven_packing_local_minimum_seed_supergraph_rigidity_edges → e ≠ s(0,7) →
    (e = s(0,4) ∨ e = s(0,6) ∨ e = s(0,8) ∨ e = s(1,8) ∨ e = s(2,7) ∨
     e = s(4,7) ∨ e = s(4,8) ∨ e = s(5,8) ∨ e = s(7,8)) := by
  decide +revert

open scoped Sym2

theorem simple_graph_seven_packing_local_minimum_seed_supergraph_rigidity :
    let E₀ : Finset (Sym2 (Fin 9)) := {s(0,1), s(0,2), s(0,3), s(0,5), s(1,2), s(1,3), s(1,4), s(1,5), s(1,6), s(1,7), s(2,3), s(2,4), s(2,5), s(2,6), s(2,8), s(3,4), s(3,5), s(3,6), s(3,7), s(3,8), s(4,5), s(4,6), s(5,6), s(5,7), s(6,7), s(6,8)}
    ∀ G : SimpleGraph (Fin 9),
      (↑E₀ : Set (Sym2 (Fin 9))) ⊆ G.edgeSet →
      (∀ P : Finset (Finset (Sym2 (Fin 9))), P ⊆ simple_graph_triangle_edge_family G →
        (P : Set (Finset (Sym2 (Fin 9)))).Pairwise Disjoint → P.card ≤ 7) →
      G.edgeSet ⊆ (↑(insert s(0,7) E₀) : Set (Sym2 (Fin 9))) := by
  intro E₀ G hsub hle e he
  by_contra hnot
  simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, not_or] at hnot
  obtain ⟨h07, hE⟩ := hnot
  have hdiag : ¬ e.IsDiag := SimpleGraph.not_isDiag_of_mem_edgeSet G he
  have hcases := simple_graph_seven_packing_local_minimum_seed_supergraph_rigidity_cases e hdiag hE h07
  rcases hcases with h | h | h | h | h | h | h | h | h
  · rw [h] at he
    exact simple_graph_seven_packing_local_minimum_seed_supergraph_rigidity_packing_contra G hsub hle (s(0,4)) he
      {{0,1,2}, {0,3,4}, {1,3,7}, {1,4,5}, {2,3,5}, {2,4,6}, {3,6,8}, {5,6,7}}
      (by decide) (by decide) (by decide)
  · rw [h] at he
    exact simple_graph_seven_packing_local_minimum_seed_supergraph_rigidity_packing_contra G hsub hle (s(0,6)) he
      {{0,1,3}, {0,2,6}, {1,2,5}, {1,6,7}, {2,3,4}, {3,5,7}, {3,6,8}, {4,5,6}}
      (by decide) (by decide) (by decide)
  · rw [h] at he
    exact simple_graph_seven_packing_local_minimum_seed_supergraph_rigidity_packing_contra G hsub hle (s(0,8)) he
      {{0,1,2}, {0,3,8}, {1,3,4}, {1,5,7}, {2,3,5}, {2,6,8}, {3,6,7}, {4,5,6}}
      (by decide) (by decide) (by decide)
  · rw [h] at he
    exact simple_graph_seven_packing_local_minimum_seed_supergraph_rigidity_packing_contra G hsub hle (s(1,8)) he
      {{0,1,2}, {0,3,5}, {1,3,4}, {1,5,7}, {1,6,8}, {2,3,8}, {2,4,5}, {3,6,7}}
      (by decide) (by decide) (by decide)
  · rw [h] at he
    exact simple_graph_seven_packing_local_minimum_seed_supergraph_rigidity_packing_contra G hsub hle (s(2,7)) he
      {{0,1,2}, {0,3,5}, {1,3,4}, {1,5,6}, {2,3,8}, {2,4,6}, {2,5,7}, {3,6,7}}
      (by decide) (by decide) (by decide)
  · rw [h] at he
    exact simple_graph_seven_packing_local_minimum_seed_supergraph_rigidity_packing_contra G hsub hle (s(4,7)) he
      {{0,1,2}, {0,3,5}, {1,3,4}, {1,5,6}, {2,3,8}, {2,4,6}, {3,6,7}, {4,5,7}}
      (by decide) (by decide) (by decide)
  · rw [h] at he
    exact simple_graph_seven_packing_local_minimum_seed_supergraph_rigidity_packing_contra G hsub hle (s(4,8)) he
      {{0,1,2}, {0,3,5}, {1,3,4}, {1,5,6}, {2,3,8}, {2,4,5}, {3,6,7}, {4,6,8}}
      (by decide) (by decide) (by decide)
  · rw [h] at he
    exact simple_graph_seven_packing_local_minimum_seed_supergraph_rigidity_packing_contra G hsub hle (s(5,8)) he
      {{0,1,2}, {0,3,5}, {1,3,4}, {1,5,7}, {2,3,8}, {2,4,5}, {3,6,7}, {5,6,8}}
      (by decide) (by decide) (by decide)
  · rw [h] at he
    exact simple_graph_seven_packing_local_minimum_seed_supergraph_rigidity_packing_contra G hsub hle (s(7,8)) he
      {{0,1,2}, {0,3,5}, {1,3,6}, {1,4,5}, {2,3,4}, {2,6,8}, {3,7,8}, {5,6,7}}
      (by decide) (by decide) (by decide)
