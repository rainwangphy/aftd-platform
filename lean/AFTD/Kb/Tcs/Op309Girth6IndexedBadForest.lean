import AFTD.Prelude
import AFTD.Kb.Tcs.Op309Girth6IndexedEdges
import AFTD.Kb.Tcs.Op309IndexedEdgeAdj
import AFTD.Kb.Tcs.Op309IndexedEdgeRich
import AFTD.Kb.Tcs.Op309FourPairConflictKernel
import AFTD.Kb.Tcs.Op309FivePaletteTwoPairs

/-!
# op309_girth6_indexed_bad_forest

Topic: graphs   Node: 618b5b0755f3

Provenance: helper lemma. OP-309 girth-six fixed-P3 obstruction; experiments 41697, 41698 and 41711–41713.

The selected indexed edges in the girth-six base pattern cannot all be rich in a proper five-coloring, under the indicated local properness conditions.
-/

set_option maxHeartbeats 4000000
local instance  aftdLocal_e2ed04bf4818df44_0 (i j : Fin 24) : Decidable (op309_indexed_edge_adj op309_girth6_indexed_edges i j) := by
  unfold op309_indexed_edge_adj op309_girth6_indexed_edges
  infer_instance

private theorem in1213_rich_five (C : Fin 24 → Fin 5) (e j k l m : Fin 24)
    (hp : ∀ j, op309_indexed_edge_adj op309_girth6_indexed_edges e j → C e ≠ C j)
    (hr : op309_indexed_edge_rich op309_girth6_indexed_edges C e)
    (hd : ([e,j,k,l,m] : List (Fin 24)).Nodup)
    (hn : ∀ x ∈ ([j,k,l,m] : List (Fin 24)), op309_indexed_edge_adj op309_girth6_indexed_edges e x) :
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

theorem op309_girth6_indexed_bad_forest
    (C : Fin 24 → Fin 5)
    (hp : ∀ i ∈ ({1,5,6,7,9,13,15,18,21,22} : Finset (Fin 24)),
      ∀ j, op309_indexed_edge_adj op309_girth6_indexed_edges i j → C i ≠ C j)
    (n02 : C 0 ≠ C 2) (n16_17 : C 16 ≠ C 17) (n03 : C 0 ≠ C 3)
    (hr : ∀ i ∈ ({1,5,6,7,9,13,15,18,21,22} : Finset (Fin 24)),
      op309_indexed_edge_rich op309_girth6_indexed_edges C i) : False := by
  set_option maxHeartbeats 4000000 in
    have l0a : ([C 6,C 7,C 8,C 0,C 3] : List (Fin 5)).Nodup := by
      apply in1213_rich_five C 6 7 8 0 3 (hp 6 (by decide)) (hr 6 (by decide)) <;> decide
    have l0b0 : ([C 7,C 6,C 8,C 11,C 16] : List (Fin 5)).Nodup := by
      apply in1213_rich_five C 7 6 8 11 16 (hp 7 (by decide)) (hr 7 (by decide)) <;> decide
    have l0b : ([C 6,C 7,C 8,C 11,C 16] : List (Fin 5)).Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.nodup_singleton, not_or] at l0b0 ⊢
      aesop
    have p0 := op309_five_palette_two_pairs (C 6) (C 7) (C 8) (C 0) (C 3) (C 11) (C 16) l0a l0b
    have l1a : ([C 21,C 22,C 23,C 4,C 10] : List (Fin 5)).Nodup := by
      apply in1213_rich_five C 21 22 23 4 10 (hp 21 (by decide)) (hr 21 (by decide)) <;> decide
    have l1b0 : ([C 22,C 21,C 23,C 14,C 17] : List (Fin 5)).Nodup := by
      apply in1213_rich_five C 22 21 23 14 17 (hp 22 (by decide)) (hr 22 (by decide)) <;> decide
    have l1b : ([C 21,C 22,C 23,C 14,C 17] : List (Fin 5)).Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.nodup_singleton, not_or] at l1b0 ⊢
      aesop
    have p1 := op309_five_palette_two_pairs (C 21) (C 22) (C 23) (C 4) (C 10) (C 14) (C 17) l1a l1b
    have l2a : ([C 1,C 9,C 12,C 0,C 2] : List (Fin 5)).Nodup := by
      apply in1213_rich_five C 1 9 12 0 2 (hp 1 (by decide)) (hr 1 (by decide)) <;> decide
    have l2b0 : ([C 9,C 1,C 12,C 10,C 11] : List (Fin 5)).Nodup := by
      apply in1213_rich_five C 9 1 12 10 11 (hp 9 (by decide)) (hr 9 (by decide)) <;> decide
    have l2b : ([C 1,C 9,C 12,C 10,C 11] : List (Fin 5)).Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.nodup_singleton, not_or] at l2b0 ⊢
      aesop
    have p2 := op309_five_palette_two_pairs (C 1) (C 9) (C 12) (C 0) (C 2) (C 10) (C 11) l2a l2b
    have l3a : ([C 15,C 18,C 2,C 16,C 17] : List (Fin 5)).Nodup := by
      apply in1213_rich_five C 15 18 2 16 17 (hp 15 (by decide)) (hr 15 (by decide)) <;> decide
    have l3b0 : ([C 18,C 15,C 2,C 19,C 20] : List (Fin 5)).Nodup := by
      apply in1213_rich_five C 18 15 2 19 20 (hp 18 (by decide)) (hr 18 (by decide)) <;> decide
    have l3b : ([C 15,C 18,C 2,C 19,C 20] : List (Fin 5)).Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, List.nodup_singleton, not_or] at l3b0 ⊢
      aesop
    have p3 := op309_five_palette_two_pairs (C 15) (C 18) (C 2) (C 16) (C 17) (C 19) (C 20) l3a l3b
    have n2_17 : C 2 ≠ C 17 := hr 15 (by decide) 2 17 (by decide) (by decide) (by decide)
    have n3_19 : C 3 ≠ C 19 := hr 5 (by decide) 3 19 (by decide) (by decide) (by decide)
    have n4_19 : C 4 ≠ C 19 := hr 5 (by decide) 4 19 (by decide) (by decide) (by decide)
    have n14_19 : C 14 ≠ C 19 := hr 13 (by decide) 14 19 (by decide) (by decide) (by decide)
    exact op309_four_pair_conflict_kernel (C 0) (C 2) (C 3) (C 4) (C 10) (C 11)
      (C 14) (C 16) (C 17) (C 19) (C 20) p0 p1 p2 p3 n02 n2_17 n3_19 n4_19 n16_17 n03 n14_19
