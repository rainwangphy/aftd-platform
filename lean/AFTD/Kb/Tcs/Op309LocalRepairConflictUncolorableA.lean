import AFTD.Prelude

/-!
# op309_local_repair_conflict_uncolorable_a

Topic: combinatorics   Node: 587ad5fef241

Provenance: helper lemma. OP-309 ten-vertex local exchange obstruction; experiments 36449, 36457, 36461.

The displayed fifteen-vertex conflict graph cannot be properly colored with five colors.
-/

set_option maxHeartbeats 0

theorem in1099_A_common_fifth (a b c d x y : Fin 5)
    (hx : [a,b,c,d,x].Nodup) (hy : [a,b,c,d,y].Nodup) : x = y := by
  by_contra hxy
  have hall : [a,b,c,d,x,y].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or,
      List.nodup_nil, and_true] at hx hy ⊢
    aesop
  have hc := hall.length_le_card
  simp at hc

theorem in1099_A_six_distinct (a b c d x y : Fin 5)
    (h : [a,b,c,d,x,y].Nodup) : False := by
  have hc := h.length_le_card
  simp at hc


def in1099_conflict_edges_A : List (Nat × Nat) := [(0,1), (0,2), (0,5), (0,9), (0,12), (0,13), (1,2), (1,3), (1,4), (1,5), (1,9), (2,5), (2,9), (2,10), (2,11), (2,13), (3,4), (3,5), (3,6), (3,7), (3,8), (3,9), (3,14), (4,5), (4,6), (4,7), (4,9), (4,14), (5,9), (6,7), (6,8), (6,14), (7,8), (7,14), (8,9), (8,10), (8,11), (8,12), (8,14), (9,10), (9,11), (9,12), (9,13), (10,11), (10,12), (10,13), (11,12), (11,13), (12,13)]

theorem op309_local_repair_conflict_uncolorable_a (f : Fin 15 → Fin 5)
    (h : ∀ i j : Fin 15, ((i.val,j.val) ∈ in1099_conflict_edges_A ∨
      (j.val,i.val) ∈ in1099_conflict_edges_A) → f i ≠ f j) : False := by
  have h_0_1 : f 0 ≠ f 1 := h 0 1 (by decide)
  have h_0_2 : f 0 ≠ f 2 := h 0 2 (by decide)
  have h_0_5 : f 0 ≠ f 5 := h 0 5 (by decide)
  have h_0_9 : f 0 ≠ f 9 := h 0 9 (by decide)
  have h_0_12 : f 0 ≠ f 12 := h 0 12 (by decide)
  have h_0_13 : f 0 ≠ f 13 := h 0 13 (by decide)
  have h_1_2 : f 1 ≠ f 2 := h 1 2 (by decide)
  have h_1_3 : f 1 ≠ f 3 := h 1 3 (by decide)
  have h_1_4 : f 1 ≠ f 4 := h 1 4 (by decide)
  have h_1_5 : f 1 ≠ f 5 := h 1 5 (by decide)
  have h_1_9 : f 1 ≠ f 9 := h 1 9 (by decide)
  have h_2_5 : f 2 ≠ f 5 := h 2 5 (by decide)
  have h_2_9 : f 2 ≠ f 9 := h 2 9 (by decide)
  have h_2_10 : f 2 ≠ f 10 := h 2 10 (by decide)
  have h_2_11 : f 2 ≠ f 11 := h 2 11 (by decide)
  have h_2_13 : f 2 ≠ f 13 := h 2 13 (by decide)
  have h_3_4 : f 3 ≠ f 4 := h 3 4 (by decide)
  have h_3_5 : f 3 ≠ f 5 := h 3 5 (by decide)
  have h_3_6 : f 3 ≠ f 6 := h 3 6 (by decide)
  have h_3_7 : f 3 ≠ f 7 := h 3 7 (by decide)
  have h_3_8 : f 3 ≠ f 8 := h 3 8 (by decide)
  have h_3_9 : f 3 ≠ f 9 := h 3 9 (by decide)
  have h_3_14 : f 3 ≠ f 14 := h 3 14 (by decide)
  have h_4_5 : f 4 ≠ f 5 := h 4 5 (by decide)
  have h_4_6 : f 4 ≠ f 6 := h 4 6 (by decide)
  have h_4_7 : f 4 ≠ f 7 := h 4 7 (by decide)
  have h_4_9 : f 4 ≠ f 9 := h 4 9 (by decide)
  have h_4_14 : f 4 ≠ f 14 := h 4 14 (by decide)
  have h_5_9 : f 5 ≠ f 9 := h 5 9 (by decide)
  have h_6_7 : f 6 ≠ f 7 := h 6 7 (by decide)
  have h_6_8 : f 6 ≠ f 8 := h 6 8 (by decide)
  have h_6_14 : f 6 ≠ f 14 := h 6 14 (by decide)
  have h_7_8 : f 7 ≠ f 8 := h 7 8 (by decide)
  have h_7_14 : f 7 ≠ f 14 := h 7 14 (by decide)
  have h_8_9 : f 8 ≠ f 9 := h 8 9 (by decide)
  have h_8_10 : f 8 ≠ f 10 := h 8 10 (by decide)
  have h_8_11 : f 8 ≠ f 11 := h 8 11 (by decide)
  have h_8_12 : f 8 ≠ f 12 := h 8 12 (by decide)
  have h_8_14 : f 8 ≠ f 14 := h 8 14 (by decide)
  have h_9_10 : f 9 ≠ f 10 := h 9 10 (by decide)
  have h_9_11 : f 9 ≠ f 11 := h 9 11 (by decide)
  have h_9_12 : f 9 ≠ f 12 := h 9 12 (by decide)
  have h_9_13 : f 9 ≠ f 13 := h 9 13 (by decide)
  have h_10_11 : f 10 ≠ f 11 := h 10 11 (by decide)
  have h_10_12 : f 10 ≠ f 12 := h 10 12 (by decide)
  have h_10_13 : f 10 ≠ f 13 := h 10 13 (by decide)
  have h_11_12 : f 11 ≠ f 12 := h 11 12 (by decide)
  have h_11_13 : f 11 ≠ f 13 := h 11 13 (by decide)
  have h_12_13 : f 12 ≠ f 13 := h 12 13 (by decide)
  have cl1 : [f 9,f 10,f 11,f 13,f 2].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, not_or, List.nodup_nil, and_true]
    aesop
  have cl2 : [f 9,f 10,f 11,f 13,f 12].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, not_or, List.nodup_nil, and_true]
    aesop
  have eq2 : f 2 = f 12 := in1099_A_common_fifth _ _ _ _ _ _ cl1 cl2
  have cl3 : [f 12,f 9,f 10,f 11,f 8].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, not_or, List.nodup_nil, and_true]
    aesop
  have cl4 : [f 2,f 9,f 10,f 11,f 13].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, not_or, List.nodup_nil, and_true]
    aesop
  have eq8_13 : f 8 = f 13 := by
    rw [← eq2] at cl3
    exact in1099_A_common_fifth _ _ _ _ _ _ cl3 cl4
  have cl5 : [f 3,f 6,f 7,f 14,f 8].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, not_or, List.nodup_nil, and_true]
    aesop
  have cl6 : [f 3,f 6,f 7,f 14,f 4].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, not_or, List.nodup_nil, and_true]
    aesop
  have eq8_4 : f 8 = f 4 := in1099_A_common_fifth _ _ _ _ _ _ cl5 cl6
  have last : [f 0,f 1,f 2,f 5,f 8,f 9].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, not_or, List.nodup_nil, and_true]
    aesop
  exact in1099_A_six_distinct _ _ _ _ _ _ last
