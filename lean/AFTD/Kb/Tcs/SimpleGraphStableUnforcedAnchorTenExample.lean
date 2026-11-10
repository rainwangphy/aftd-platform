import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIn693TenSeedPackingNumber
import AFTD.Kb.Tcs.SimpleGraphIn693TenSeedPairStable
import AFTD.Kb.Tcs.SimpleGraphTriangleEdgeFamily
import AFTD.Kb.Tcs.FiniteVertexSetEdgeEncoding
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber

/-!
# simple_graph_stable_unforced_anchor_ten_example

Topic: graphs   Node: 99e40c426908

Provenance: helper lemma. Concrete ten-vertex example from experiments 20301–20303, 20312 and 20378; see state/campaigns/triangle_reductions/private_k4_in694.md. Related forced-triangle structure is in https://arxiv.org/abs/2001.00257, Section 3. Literature checked 2026-11-10.

A two-edge-stable graph has a full-support maximum packing with a fully forced K4 face whose internal anchor lies only in unforced packed triangles.
-/

open scoped Sym2
lemma sharp_family : simple_graph_triangle_edge_family sharp_G =
    sharp_T.toFinset.image finite_vertex_set_edge_encoding := by
  classical
  ext x
  simp only [simple_graph_triangle_edge_family, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, sharp_clique_mem ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, sharp_T_clique t ht, rfl⟩


def sharp_bad_P : Finset (Finset (Fin 10)) := {{0,1,5},{0,2,3},{2,8,9},{2,6,7},{3,7,8},{5,6,8},{3,6,9},{4,5,9}}
set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
theorem sharp_bad_cliques : ∀ t ∈ sharp_bad_P, sharp_G.IsNClique 3 t := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
theorem sharp_bad_disjoint : (sharp_bad_P : Set (Finset (Fin 10))).Pairwise (fun a b => (a ∩ b).card ≤ 1) := by decide +kernel
set_option maxRecDepth 100000 in
theorem sharp_bad_support : sharp_bad_P.biUnion id = Finset.univ := by decide +kernel
set_option maxRecDepth 100000 in
theorem sharp_bad_card : sharp_bad_P.card = 8 := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
theorem sharp_bad_forced : finite_vertex_set_edge_encoding ({2,8,9} : Finset (Fin 10)) ⊆
  (((simple_graph_triangle_edge_family sharp_G).filter
    (fun t => (t ∩ sharp_bad_P.biUnion finite_vertex_set_edge_encoding).card = 1)).biUnion id) := by
  rw [sharp_family]
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
theorem sharp_bad_anchor_unforced : ∀ q ∈ sharp_bad_P, (1 : Fin 10) ∈ q →
  Disjoint (finite_vertex_set_edge_encoding q)
    (((simple_graph_triangle_edge_family sharp_G).filter
      (fun t => (t ∩ sharp_bad_P.biUnion finite_vertex_set_edge_encoding).card = 1)).biUnion id) := by
  rw [sharp_family]
  decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 30000000 in
theorem sharp_bad_k4 : sharp_G.IsNClique 4 ({1,2,8,9} : Finset (Fin 10)) := by decide +kernel

theorem simple_graph_stable_unforced_anchor_ten_example : let P : Finset (Finset (Fin 10)) := {{0,1,5},{0,2,3},{2,8,9},{2,6,7},{3,7,8},{5,6,8},{3,6,9},{4,5,9}}; ∃ G : SimpleGraph (Fin 10), (∀ t ∈ P, G.IsNClique 3 t) ∧ (P : Set (Finset (Fin 10))).Pairwise (fun t u => (t ∩ u).card ≤ 1) ∧ P.card = simple_graph_triangle_packing_number G ∧ P.biUnion id = Finset.univ ∧ (∀ e f : Sym2 (Fin 10), e ∈ G.edgeSet → f ∈ G.edgeSet → e ≠ f → simple_graph_triangle_packing_number (G.deleteEdges {e,f}) = simple_graph_triangle_packing_number G) ∧ G.IsNClique 4 ({1,2,8,9} : Finset (Fin 10)) ∧ ({2,8,9} : Finset (Fin 10)) ∈ P ∧ finite_vertex_set_edge_encoding ({2,8,9} : Finset (Fin 10)) ⊆ (((simple_graph_triangle_edge_family G).filter (fun t => (t ∩ P.biUnion finite_vertex_set_edge_encoding).card = 1)).biUnion id) ∧ (∃ q ∈ P, (1 : Fin 10) ∈ q) ∧ (∀ q ∈ P, (1 : Fin 10) ∈ q → Disjoint (finite_vertex_set_edge_encoding q) (((simple_graph_triangle_edge_family G).filter (fun t => (t ∩ P.biUnion finite_vertex_set_edge_encoding).card = 1)).biUnion id)) := by
  classical
  dsimp only
  refine ⟨sharp_G, sharp_bad_cliques, sharp_bad_disjoint, ?_, sharp_bad_support,
    sharp_stable, sharp_bad_k4, ?_, sharp_bad_forced, ?_, sharp_bad_anchor_unforced⟩
  · change sharp_bad_P.card = simple_graph_triangle_packing_number sharp_G
    rw [sharp_bad_card, sharp_pack_eq]
  · decide +kernel
  · exact ⟨{0,1,5}, by decide +kernel, by decide +kernel⟩
