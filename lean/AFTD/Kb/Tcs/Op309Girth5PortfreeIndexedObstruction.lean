import AFTD.Prelude
import AFTD.Kb.Tcs.Op309Girth5TwentyIndexedEdges
import AFTD.Kb.Tcs.Op309IndexedEdgeAdj
import AFTD.Kb.Tcs.Op309IndexedEdgeRich
import AFTD.Kb.Tcs.Op309FivePaletteTwoPairs
import AFTD.Kb.Tcs.Op309Girth5PortfreeSixClique

/-!
# op309_girth5_portfree_indexed_obstruction

Topic: graphs   Node: 705c88b123db

Provenance: helper lemma. OP-309; girth-five port-free fixed-forest certificate, experiments 41785–41788 and 41796.

The selected P3 edges in the indexed girth-five pattern cannot all be rich under the displayed local five-color conditions.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
local instance  aftdLocal_f72532eea24b9ceb_0 (i j : Fin 30) : Decidable (op309_indexed_edge_adj op309_girth5_twenty_indexed_edges i j) := by
  unfold op309_indexed_edge_adj op309_girth5_twenty_indexed_edges
  infer_instance

private theorem in1213_girth5_portfree_rich_five (C : Fin 30 → Fin 5) (e j k l m : Fin 30)
    (hp : ∀ j, op309_indexed_edge_adj op309_girth5_twenty_indexed_edges e j → C e ≠ C j)
    (hr : op309_indexed_edge_rich op309_girth5_twenty_indexed_edges C e)
    (hd : ([e,j,k,l,m] : List (Fin 30)).Nodup)
    (hn : ∀ x ∈ ([j,k,l,m] : List (Fin 30)), op309_indexed_edge_adj op309_girth5_twenty_indexed_edges e x) :
    ([C e,C j,C k,C l,C m] : List (Fin 5)).Nodup := by
  have hj := hn j (by simp)
  have hk := hn k (by simp)
  have hl := hn l (by simp)
  have hm := hn m (by simp)
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
    not_or, not_false_eq_true, and_true] at hd ⊢
  dsimp [op309_indexed_edge_rich] at hr
  rcases hd with ⟨⟨_,_,_,_⟩,⟨hjk,hjl,hjm⟩,⟨hkl,hkm⟩,hlm⟩
  exact ⟨⟨hp j hj, hp k hk, hp l hl, hp m hm⟩,
    ⟨hr j k hj hk hjk, hr j l hj hl hjl, hr j m hj hm hjm⟩,
    ⟨hr k l hk hl hkl, hr k m hk hm hkm⟩, hr l m hl hm hlm⟩

theorem op309_girth5_portfree_indexed_obstruction
    (C : Fin 30 → Fin 5)
    (hp : ∀ i ∈ ({0,4,6,8,9,13,14,17,18,21,25,29} : Finset (Fin 30)),
      ∀ j, op309_indexed_edge_adj op309_girth5_twenty_indexed_edges i j → C i ≠ C j)
    (hr : ∀ i ∈ ({0,4,6,8,9,13,14,17,18,21,25,29} : Finset (Fin 30)),
      op309_indexed_edge_rich op309_girth5_twenty_indexed_edges C i)
    (n2_26 : C 2 ≠ C 26)
    (n15_20 : C 15 ≠ C 20)
    (n26_27 : C 26 ≠ C 27)
    : False := by
  set_option maxHeartbeats 4000000 in
    have a0 : ([C 6,C 8,C 7,C 23,C 24] : List (Fin 5)).Nodup := by
      apply in1213_girth5_portfree_rich_five C 6 8 7 23 24 (hp 6 (by decide)) (hr 6 (by decide)) <;> decide
    have b00 : ([C 8,C 6,C 7,C 22,C 28] : List (Fin 5)).Nodup := by
      apply in1213_girth5_portfree_rich_five C 8 6 7 22 28 (hp 8 (by decide)) (hr 8 (by decide)) <;> decide
    have b0 : ([C 6,C 8,C 7,C 22,C 28] : List (Fin 5)).Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.nodup_singleton, not_or] at b00 ⊢
      aesop
    have p0 := op309_five_palette_two_pairs (C 6) (C 8) (C 7) (C 23) (C 24) (C 22) (C 28) a0 b0
    have a1 : ([C 9,C 13,C 12,C 10,C 11] : List (Fin 5)).Nodup := by
      apply in1213_girth5_portfree_rich_five C 9 13 12 10 11 (hp 9 (by decide)) (hr 9 (by decide)) <;> decide
    have b10 : ([C 13,C 9,C 12,C 19,C 28] : List (Fin 5)).Nodup := by
      apply in1213_girth5_portfree_rich_five C 13 9 12 19 28 (hp 13 (by decide)) (hr 13 (by decide)) <;> decide
    have b1 : ([C 9,C 13,C 12,C 19,C 28] : List (Fin 5)).Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.nodup_singleton, not_or] at b10 ⊢
      aesop
    have p1 := op309_five_palette_two_pairs (C 9) (C 13) (C 12) (C 10) (C 11) (C 19) (C 28) a1 b1
    have a2 : ([C 0,C 18,C 19,C 1,C 2] : List (Fin 5)).Nodup := by
      apply in1213_girth5_portfree_rich_five C 0 18 19 1 2 (hp 0 (by decide)) (hr 0 (by decide)) <;> decide
    have b20 : ([C 18,C 0,C 19,C 5,C 7] : List (Fin 5)).Nodup := by
      apply in1213_girth5_portfree_rich_five C 18 0 19 5 7 (hp 18 (by decide)) (hr 18 (by decide)) <;> decide
    have b2 : ([C 0,C 18,C 19,C 5,C 7] : List (Fin 5)).Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.nodup_singleton, not_or] at b20 ⊢
      aesop
    have p2 := op309_five_palette_two_pairs (C 0) (C 18) (C 19) (C 1) (C 2) (C 5) (C 7) a2 b2
    have a3 : ([C 4,C 14,C 10,C 3,C 5] : List (Fin 5)).Nodup := by
      apply in1213_girth5_portfree_rich_five C 4 14 10 3 5 (hp 4 (by decide)) (hr 4 (by decide)) <;> decide
    have b30 : ([C 14,C 4,C 10,C 15,C 16] : List (Fin 5)).Nodup := by
      apply in1213_girth5_portfree_rich_five C 14 4 10 15 16 (hp 14 (by decide)) (hr 14 (by decide)) <;> decide
    have b3 : ([C 4,C 14,C 10,C 15,C 16] : List (Fin 5)).Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.nodup_singleton, not_or] at b30 ⊢
      aesop
    have p3 := op309_five_palette_two_pairs (C 4) (C 14) (C 10) (C 3) (C 5) (C 15) (C 16) a3 b3
    have a4 : ([C 17,C 25,C 16,C 3,C 12] : List (Fin 5)).Nodup := by
      apply in1213_girth5_portfree_rich_five C 17 25 16 3 12 (hp 17 (by decide)) (hr 17 (by decide)) <;> decide
    have b40 : ([C 25,C 17,C 16,C 23,C 26] : List (Fin 5)).Nodup := by
      apply in1213_girth5_portfree_rich_five C 25 17 16 23 26 (hp 25 (by decide)) (hr 25 (by decide)) <;> decide
    have b4 : ([C 17,C 25,C 16,C 23,C 26] : List (Fin 5)).Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.nodup_singleton, not_or] at b40 ⊢
      aesop
    have p4 := op309_five_palette_two_pairs (C 17) (C 25) (C 16) (C 3) (C 12) (C 23) (C 26) a4 b4
    have a5 : ([C 21,C 29,C 24,C 1,C 20] : List (Fin 5)).Nodup := by
      apply in1213_girth5_portfree_rich_five C 21 29 24 1 20 (hp 21 (by decide)) (hr 21 (by decide)) <;> decide
    have b50 : ([C 29,C 21,C 24,C 11,C 27] : List (Fin 5)).Nodup := by
      apply in1213_girth5_portfree_rich_five C 29 21 24 11 27 (hp 29 (by decide)) (hr 29 (by decide)) <;> decide
    have b5 : ([C 21,C 29,C 24,C 11,C 27] : List (Fin 5)).Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.nodup_singleton, not_or] at b50 ⊢
      aesop
    have p5 := op309_five_palette_two_pairs (C 21) (C 29) (C 24) (C 1) (C 20) (C 11) (C 27) a5 b5
    have p0partial : C 24 = C 28 ∨ C 23 = C 28 := by rcases p0 with h | h <;> aesop
    have n1_2 : C 1 ≠ C 2 := hr 0 (by decide) 1 2 (by decide) (by decide) (by decide)
    have n1_19 : C 1 ≠ C 19 := hr 0 (by decide) 1 19 (by decide) (by decide) (by decide)
    have n1_20 : C 1 ≠ C 20 := hr 21 (by decide) 1 20 (by decide) (by decide) (by decide)
    have n1_24 : C 1 ≠ C 24 := hr 21 (by decide) 1 24 (by decide) (by decide) (by decide)
    have n2_19 : C 2 ≠ C 19 := hr 0 (by decide) 2 19 (by decide) (by decide) (by decide)
    have n3_5 : C 3 ≠ C 5 := hr 4 (by decide) 3 5 (by decide) (by decide) (by decide)
    have n3_10 : C 3 ≠ C 10 := hr 4 (by decide) 3 10 (by decide) (by decide) (by decide)
    have n3_12 : C 3 ≠ C 12 := hr 17 (by decide) 3 12 (by decide) (by decide) (by decide)
    have n3_16 : C 3 ≠ C 16 := hr 17 (by decide) 3 16 (by decide) (by decide) (by decide)
    have n5_10 : C 5 ≠ C 10 := hr 4 (by decide) 5 10 (by decide) (by decide) (by decide)
    have n7_23 : C 7 ≠ C 23 := hr 6 (by decide) 7 23 (by decide) (by decide) (by decide)
    have n7_24 : C 7 ≠ C 24 := hr 6 (by decide) 7 24 (by decide) (by decide) (by decide)
    have n7_28 : C 7 ≠ C 28 := hr 8 (by decide) 7 28 (by decide) (by decide) (by decide)
    have n10_11 : C 10 ≠ C 11 := hr 9 (by decide) 10 11 (by decide) (by decide) (by decide)
    have n10_12 : C 10 ≠ C 12 := hr 9 (by decide) 10 12 (by decide) (by decide) (by decide)
    have n10_15 : C 10 ≠ C 15 := hr 14 (by decide) 10 15 (by decide) (by decide) (by decide)
    have n11_12 : C 11 ≠ C 12 := hr 9 (by decide) 11 12 (by decide) (by decide) (by decide)
    have n11_24 : C 11 ≠ C 24 := hr 29 (by decide) 11 24 (by decide) (by decide) (by decide)
    have n12_16 : C 12 ≠ C 16 := hr 17 (by decide) 12 16 (by decide) (by decide) (by decide)
    have n12_28 : C 12 ≠ C 28 := hr 13 (by decide) 12 28 (by decide) (by decide) (by decide)
    exact op309_girth5_portfree_six_clique (C 1) (C 2) (C 3) (C 5) (C 7) (C 10) (C 11) (C 12) (C 15) (C 16) (C 19) (C 20) (C 23) (C 24) (C 26) (C 27) (C 28)
      p0partial p1 p2 p3 p4 p5
      n1_2 n1_19 n1_20 n1_24 n2_19 n2_26 n3_5 n3_10 n3_12 n3_16 n5_10 n7_23 n7_24 n7_28 n10_11 n10_12 n10_15 n11_12 n11_24 n12_16 n12_28 n15_20 n26_27
