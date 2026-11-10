import AFTD.Prelude

/-!
# finite_five_vertex_triangle_packing_card_le_two

Topic: combinatorics   Node: 9320340318e9

Provenance: helper lemma. Five-vertex block bound for simple_graph_dense_high_degree_unforced_internal_k4_anchor_counterexample.

Any family of three-element subsets of a five-element set with pairwise intersections of at most one has at most two members.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace In704Five
def in704_triangles5 : Finset (Finset (Fin 5)) :=
  {{0,1,2},{0,1,3},{0,1,4},{0,2,3},{0,2,4},{0,3,4},{1,2,3},{1,2,4},{1,3,4},{2,3,4}}

lemma in704_triangles5_complete (t : Finset (Fin 5)) (ht : t.card = 3) : t ∈ in704_triangles5 := by
  have h : ∀ t : Finset (Fin 5), t.card = 3 → t ∈ in704_triangles5 := by decide
  exact h t ht

lemma in704_three_impossible :
    ∀ a ∈ in704_triangles5, ∀ b ∈ in704_triangles5, ∀ c ∈ in704_triangles5,
      (a ∩ b).card ≤ 1 → (a ∩ c).card ≤ 1 → (b ∩ c).card ≤ 1 →
      a = b ∨ a = c ∨ b = c := by
  decide

theorem in704_five_triangle_packing_card_le_two (P : Finset (Finset (Fin 5)))
    (htri : ∀ t ∈ P, t.card = 3)
    (hpack : (P : Set (Finset (Fin 5))).Pairwise (fun a b => (a ∩ b).card ≤ 1)) :
    P.card ≤ 2 := by
  by_contra h
  have hcard : 2 < P.card := by omega
  obtain ⟨a,ha,b,hb,c,hc,hab,hac,hbc⟩ := Finset.two_lt_card.mp hcard
  have hab' := hpack ha hb hab
  have hac' := hpack ha hc hac
  have hbc' := hpack hb hc hbc
  rcases in704_three_impossible a (in704_triangles5_complete a (htri a ha))
      b (in704_triangles5_complete b (htri b hb))
      c (in704_triangles5_complete c (htri c hc)) hab' hac' hbc' with h | h | h
  · exact hab h
  · exact hac h
  · exact hbc h

end In704Five

theorem finite_five_vertex_triangle_packing_card_le_two (P : Finset (Finset (Fin 5))) (htri : ∀ t ∈ P, t.card = 3) (hpack : (P : Set (Finset (Fin 5))).Pairwise (fun a b => (a ∩ b).card ≤ 1)) : P.card ≤ 2 := by
  exact In704Five.in704_five_triangle_packing_card_le_two P htri hpack
