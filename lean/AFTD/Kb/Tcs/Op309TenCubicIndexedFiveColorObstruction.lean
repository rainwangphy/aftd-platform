import AFTD.Prelude
import AFTD.Kb.Tcs.Op309TenCubicStarSelectionBooleanKernel

/-!
# op309_ten_cubic_indexed_five_color_obstruction

Topic: graphs   Node: fd561785f14a

Provenance: helper lemma. OP-309; indexed finite six-color obstruction for the previously used double-diamond graph, experiments 42024, 42026 and 42028.

For the fifteen indexed edges of the double-diamond graph, the listed total-domination, forbidden-path and triangle constraints on selected edges and the listed properness and selected-richness inequalities cannot all hold for five colors.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem op309_ten_cubic_indexed_five_color_obstruction (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 : Bool) (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 : Fin 5)
  (hdom : (b1 = true ∨ b2 = true ∨ b12 = true ∨ b13 = true) ∧
    (b0 = true ∨ b2 = true ∨ b9 = true ∨ b12 = true) ∧
    (b0 = true ∨ b1 = true ∨ b10 = true ∨ b13 = true) ∧
    (b4 = true ∨ b5 = true ∨ b6 = true ∨ b14 = true) ∧
    (b3 = true ∨ b5 = true ∨ b7 = true ∨ b11 = true) ∧
    (b3 = true ∨ b4 = true ∨ b8 = true ∨ b14 = true) ∧
    (b3 = true ∨ b7 = true ∨ b8 = true ∨ b14 = true) ∧
    (b4 = true ∨ b6 = true ∨ b8 = true ∨ b11 = true) ∧
    (b5 = true ∨ b6 = true ∨ b7 = true ∨ b14 = true) ∧
    (b1 = true ∨ b10 = true ∨ b11 = true ∨ b12 = true) ∧
    (b2 = true ∨ b9 = true ∨ b11 = true ∨ b13 = true) ∧
    (b4 = true ∨ b7 = true ∨ b9 = true ∨ b10 = true) ∧
    (b0 = true ∨ b1 = true ∨ b9 = true ∨ b13 = true) ∧
    (b0 = true ∨ b2 = true ∨ b10 = true ∨ b12 = true) ∧
    (b3 = true ∨ b5 = true ∨ b6 = true ∨ b8 = true))
  (htri : ¬ (b0 = true ∧ b1 = true ∧ b12 = true) ∧
    ¬ (b0 = true ∧ b2 = true ∧ b13 = true) ∧
    ¬ (b3 = true ∧ b5 = true ∧ b14 = true) ∧
    ¬ (b6 = true ∧ b8 = true ∧ b14 = true))
  (hpath : ¬ (b0 = true ∧ b1 = true ∧ b9 = true) ∧
    ¬ (b0 = true ∧ b1 = true ∧ b13 = true) ∧
    ¬ (b0 = true ∧ b2 = true ∧ b10 = true) ∧
    ¬ (b0 = true ∧ b2 = true ∧ b12 = true) ∧
    ¬ (b0 = true ∧ b9 = true ∧ b12 = true) ∧
    ¬ (b0 = true ∧ b10 = true ∧ b13 = true) ∧
    ¬ (b1 = true ∧ b2 = true ∧ b9 = true) ∧
    ¬ (b1 = true ∧ b2 = true ∧ b10 = true) ∧
    ¬ (b1 = true ∧ b2 = true ∧ b12 = true) ∧
    ¬ (b1 = true ∧ b2 = true ∧ b13 = true) ∧
    ¬ (b1 = true ∧ b9 = true ∧ b10 = true) ∧
    ¬ (b1 = true ∧ b9 = true ∧ b11 = true) ∧
    ¬ (b1 = true ∧ b12 = true ∧ b13 = true) ∧
    ¬ (b2 = true ∧ b9 = true ∧ b10 = true) ∧
    ¬ (b2 = true ∧ b10 = true ∧ b11 = true) ∧
    ¬ (b2 = true ∧ b12 = true ∧ b13 = true) ∧
    ¬ (b3 = true ∧ b4 = true ∧ b6 = true) ∧
    ¬ (b3 = true ∧ b4 = true ∧ b7 = true) ∧
    ¬ (b3 = true ∧ b4 = true ∧ b11 = true) ∧
    ¬ (b3 = true ∧ b4 = true ∧ b14 = true) ∧
    ¬ (b3 = true ∧ b5 = true ∧ b6 = true) ∧
    ¬ (b3 = true ∧ b5 = true ∧ b8 = true) ∧
    ¬ (b3 = true ∧ b6 = true ∧ b7 = true) ∧
    ¬ (b3 = true ∧ b6 = true ∧ b8 = true) ∧
    ¬ (b3 = true ∧ b8 = true ∧ b14 = true) ∧
    ¬ (b4 = true ∧ b5 = true ∧ b7 = true) ∧
    ¬ (b4 = true ∧ b5 = true ∧ b8 = true) ∧
    ¬ (b4 = true ∧ b5 = true ∧ b11 = true) ∧
    ¬ (b4 = true ∧ b5 = true ∧ b14 = true) ∧
    ¬ (b4 = true ∧ b6 = true ∧ b7 = true) ∧
    ¬ (b4 = true ∧ b7 = true ∧ b8 = true) ∧
    ¬ (b4 = true ∧ b9 = true ∧ b11 = true) ∧
    ¬ (b4 = true ∧ b10 = true ∧ b11 = true) ∧
    ¬ (b5 = true ∧ b6 = true ∧ b8 = true) ∧
    ¬ (b5 = true ∧ b6 = true ∧ b14 = true) ∧
    ¬ (b5 = true ∧ b7 = true ∧ b8 = true) ∧
    ¬ (b6 = true ∧ b7 = true ∧ b11 = true) ∧
    ¬ (b6 = true ∧ b7 = true ∧ b14 = true) ∧
    ¬ (b7 = true ∧ b8 = true ∧ b11 = true) ∧
    ¬ (b7 = true ∧ b8 = true ∧ b14 = true) ∧
    ¬ (b7 = true ∧ b9 = true ∧ b11 = true) ∧
    ¬ (b7 = true ∧ b10 = true ∧ b11 = true) ∧
    ¬ (b9 = true ∧ b10 = true ∧ b12 = true) ∧
    ¬ (b9 = true ∧ b10 = true ∧ b13 = true) ∧
    ¬ (b9 = true ∧ b11 = true ∧ b12 = true) ∧
    ¬ (b9 = true ∧ b12 = true ∧ b13 = true) ∧
    ¬ (b10 = true ∧ b11 = true ∧ b13 = true) ∧
    ¬ (b10 = true ∧ b12 = true ∧ b13 = true))
  (p_0_1 : c0 ≠ c1)
  (p_0_2 : c0 ≠ c2)
  (p_0_12 : c0 ≠ c12)
  (p_0_13 : c0 ≠ c13)
  (p_1_2 : c1 ≠ c2)
  (p_1_9 : c1 ≠ c9)
  (p_1_12 : c1 ≠ c12)
  (p_2_10 : c2 ≠ c10)
  (p_2_13 : c2 ≠ c13)
  (p_3_4 : c3 ≠ c4)
  (p_3_5 : c3 ≠ c5)
  (p_3_6 : c3 ≠ c6)
  (p_3_14 : c3 ≠ c14)
  (p_4_5 : c4 ≠ c5)
  (p_5_8 : c5 ≠ c8)
  (p_5_14 : c5 ≠ c14)
  (p_6_7 : c6 ≠ c7)
  (p_6_8 : c6 ≠ c8)
  (p_6_14 : c6 ≠ c14)
  (p_7_8 : c7 ≠ c8)
  (p_8_14 : c8 ≠ c14)
  (p_9_12 : c9 ≠ c12)
  (p_10_13 : c10 ≠ c13)
  (p_12_13 : c12 ≠ c13)
  (r_0_1_13 : b0 = true → c1 ≠ c13)
  (r_0_2_12 : b0 = true → c2 ≠ c12)
  (r_1_0_9 : b1 = true → c0 ≠ c9)
  (r_1_2_9 : b1 = true → c2 ≠ c9)
  (r_1_2_12 : b1 = true → c2 ≠ c12)
  (r_2_0_10 : b2 = true → c0 ≠ c10)
  (r_2_1_10 : b2 = true → c1 ≠ c10)
  (r_2_1_13 : b2 = true → c1 ≠ c13)
  (r_3_4_6 : b3 = true → c4 ≠ c6)
  (r_3_4_14 : b3 = true → c4 ≠ c14)
  (r_3_5_6 : b3 = true → c5 ≠ c6)
  (r_4_3_7 : b4 = true → c3 ≠ c7)
  (r_4_5_7 : b4 = true → c5 ≠ c7)
  (r_5_3_8 : b5 = true → c3 ≠ c8)
  (r_5_4_8 : b5 = true → c4 ≠ c8)
  (r_5_4_14 : b5 = true → c4 ≠ c14)
  (r_6_3_7 : b6 = true → c3 ≠ c7)
  (r_6_3_8 : b6 = true → c3 ≠ c8)
  (r_6_7_14 : b6 = true → c7 ≠ c14)
  (r_7_4_6 : b7 = true → c4 ≠ c6)
  (r_7_4_8 : b7 = true → c4 ≠ c8)
  (r_8_5_6 : b8 = true → c5 ≠ c6)
  (r_8_5_7 : b8 = true → c5 ≠ c7)
  (r_8_7_14 : b8 = true → c7 ≠ c14)
  (r_9_1_10 : b9 = true → c1 ≠ c10)
  (r_9_10_12 : b9 = true → c10 ≠ c12)
  (r_10_2_9 : b10 = true → c2 ≠ c9)
  (r_10_9_13 : b10 = true → c9 ≠ c13)
  (r_12_0_9 : b12 = true → c0 ≠ c9)
  (r_12_1_13 : b12 = true → c1 ≠ c13)
  (r_12_9_13 : b12 = true → c9 ≠ c13)
  (r_13_0_10 : b13 = true → c0 ≠ c10)
  (r_13_2_12 : b13 = true → c2 ≠ c12)
  (r_13_10_12 : b13 = true → c10 ≠ c12)
  (r_14_3_8 : b14 = true → c3 ≠ c8)
  (r_14_5_6 : b14 = true → c5 ≠ c6) : False := by
  have hk := op309_ten_cubic_star_selection_boolean_kernel b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 hdom htri hpath
  rcases hk with ⟨t3, t5⟩ | ⟨t6, t8⟩ | ⟨t0, t2, t9⟩ | ⟨t0, t1, t10⟩ | ⟨t1, t12⟩ | ⟨t0, t10, t12⟩ | ⟨t2, t13⟩ | ⟨t0, t9, t13⟩ | ⟨t4, t6, t14⟩ | ⟨t3, t7, t14⟩ | ⟨t5, t7, t14⟩ | ⟨t4, t8, t14⟩
  · have hn : [c3, c4, c5, c6, c8, c14].Nodup := by
      have h_3_4 : c3 ≠ c4 := p_3_4
      have h_3_5 : c3 ≠ c5 := p_3_5
      have h_3_6 : c3 ≠ c6 := p_3_6
      have h_3_8 : c3 ≠ c8 := r_5_3_8 t5
      have h_3_14 : c3 ≠ c14 := p_3_14
      have h_4_5 : c4 ≠ c5 := p_4_5
      have h_4_6 : c4 ≠ c6 := r_3_4_6 t3
      have h_4_8 : c4 ≠ c8 := r_5_4_8 t5
      have h_4_14 : c4 ≠ c14 := r_3_4_14 t3
      have h_5_6 : c5 ≠ c6 := r_3_5_6 t3
      have h_5_8 : c5 ≠ c8 := p_5_8
      have h_5_14 : c5 ≠ c14 := p_5_14
      have h_6_8 : c6 ≠ c8 := p_6_8
      have h_6_14 : c6 ≠ c14 := p_6_14
      have h_8_14 : c8 ≠ c14 := p_8_14
      simp [h_3_4, h_3_5, h_3_6, h_3_8, h_3_14, h_4_5, h_4_6, h_4_8, h_4_14, h_5_6, h_5_8, h_5_14, h_6_8, h_6_14, h_8_14]
    have hc := List.Nodup.length_le_card hn
    norm_num at hc
  · have hn : [c3, c5, c6, c7, c8, c14].Nodup := by
      have h_3_5 : c3 ≠ c5 := p_3_5
      have h_3_6 : c3 ≠ c6 := p_3_6
      have h_3_7 : c3 ≠ c7 := r_6_3_7 t6
      have h_3_8 : c3 ≠ c8 := r_6_3_8 t6
      have h_3_14 : c3 ≠ c14 := p_3_14
      have h_5_6 : c5 ≠ c6 := r_8_5_6 t8
      have h_5_7 : c5 ≠ c7 := r_8_5_7 t8
      have h_5_8 : c5 ≠ c8 := p_5_8
      have h_5_14 : c5 ≠ c14 := p_5_14
      have h_6_7 : c6 ≠ c7 := p_6_7
      have h_6_8 : c6 ≠ c8 := p_6_8
      have h_6_14 : c6 ≠ c14 := p_6_14
      have h_7_8 : c7 ≠ c8 := p_7_8
      have h_7_14 : c7 ≠ c14 := r_6_7_14 t6
      have h_8_14 : c8 ≠ c14 := p_8_14
      simp [h_3_5, h_3_6, h_3_7, h_3_8, h_3_14, h_5_6, h_5_7, h_5_8, h_5_14, h_6_7, h_6_8, h_6_14, h_7_8, h_7_14, h_8_14]
    have hc := List.Nodup.length_le_card hn
    norm_num at hc
  · have hn : [c0, c1, c2, c10, c12, c13].Nodup := by
      have h_0_1 : c0 ≠ c1 := p_0_1
      have h_0_2 : c0 ≠ c2 := p_0_2
      have h_0_10 : c0 ≠ c10 := r_2_0_10 t2
      have h_0_12 : c0 ≠ c12 := p_0_12
      have h_0_13 : c0 ≠ c13 := p_0_13
      have h_1_2 : c1 ≠ c2 := p_1_2
      have h_1_10 : c1 ≠ c10 := r_2_1_10 t2
      have h_1_12 : c1 ≠ c12 := p_1_12
      have h_1_13 : c1 ≠ c13 := r_0_1_13 t0
      have h_2_10 : c2 ≠ c10 := p_2_10
      have h_2_12 : c2 ≠ c12 := r_0_2_12 t0
      have h_2_13 : c2 ≠ c13 := p_2_13
      have h_10_12 : c10 ≠ c12 := r_9_10_12 t9
      have h_10_13 : c10 ≠ c13 := p_10_13
      have h_12_13 : c12 ≠ c13 := p_12_13
      simp [h_0_1, h_0_2, h_0_10, h_0_12, h_0_13, h_1_2, h_1_10, h_1_12, h_1_13, h_2_10, h_2_12, h_2_13, h_10_12, h_10_13, h_12_13]
    have hc := List.Nodup.length_le_card hn
    norm_num at hc
  · have hn : [c0, c1, c2, c9, c12, c13].Nodup := by
      have h_0_1 : c0 ≠ c1 := p_0_1
      have h_0_2 : c0 ≠ c2 := p_0_2
      have h_0_9 : c0 ≠ c9 := r_1_0_9 t1
      have h_0_12 : c0 ≠ c12 := p_0_12
      have h_0_13 : c0 ≠ c13 := p_0_13
      have h_1_2 : c1 ≠ c2 := p_1_2
      have h_1_9 : c1 ≠ c9 := p_1_9
      have h_1_12 : c1 ≠ c12 := p_1_12
      have h_1_13 : c1 ≠ c13 := r_0_1_13 t0
      have h_2_9 : c2 ≠ c9 := r_1_2_9 t1
      have h_2_12 : c2 ≠ c12 := r_0_2_12 t0
      have h_2_13 : c2 ≠ c13 := p_2_13
      have h_9_12 : c9 ≠ c12 := p_9_12
      have h_9_13 : c9 ≠ c13 := r_10_9_13 t10
      have h_12_13 : c12 ≠ c13 := p_12_13
      simp [h_0_1, h_0_2, h_0_9, h_0_12, h_0_13, h_1_2, h_1_9, h_1_12, h_1_13, h_2_9, h_2_12, h_2_13, h_9_12, h_9_13, h_12_13]
    have hc := List.Nodup.length_le_card hn
    norm_num at hc
  · have hn : [c0, c1, c2, c9, c12, c13].Nodup := by
      have h_0_1 : c0 ≠ c1 := p_0_1
      have h_0_2 : c0 ≠ c2 := p_0_2
      have h_0_9 : c0 ≠ c9 := r_1_0_9 t1
      have h_0_12 : c0 ≠ c12 := p_0_12
      have h_0_13 : c0 ≠ c13 := p_0_13
      have h_1_2 : c1 ≠ c2 := p_1_2
      have h_1_9 : c1 ≠ c9 := p_1_9
      have h_1_12 : c1 ≠ c12 := p_1_12
      have h_1_13 : c1 ≠ c13 := r_12_1_13 t12
      have h_2_9 : c2 ≠ c9 := r_1_2_9 t1
      have h_2_12 : c2 ≠ c12 := r_1_2_12 t1
      have h_2_13 : c2 ≠ c13 := p_2_13
      have h_9_12 : c9 ≠ c12 := p_9_12
      have h_9_13 : c9 ≠ c13 := r_12_9_13 t12
      have h_12_13 : c12 ≠ c13 := p_12_13
      simp [h_0_1, h_0_2, h_0_9, h_0_12, h_0_13, h_1_2, h_1_9, h_1_12, h_1_13, h_2_9, h_2_12, h_2_13, h_9_12, h_9_13, h_12_13]
    have hc := List.Nodup.length_le_card hn
    norm_num at hc
  · have hn : [c0, c1, c2, c9, c12, c13].Nodup := by
      have h_0_1 : c0 ≠ c1 := p_0_1
      have h_0_2 : c0 ≠ c2 := p_0_2
      have h_0_9 : c0 ≠ c9 := r_12_0_9 t12
      have h_0_12 : c0 ≠ c12 := p_0_12
      have h_0_13 : c0 ≠ c13 := p_0_13
      have h_1_2 : c1 ≠ c2 := p_1_2
      have h_1_9 : c1 ≠ c9 := p_1_9
      have h_1_12 : c1 ≠ c12 := p_1_12
      have h_1_13 : c1 ≠ c13 := r_0_1_13 t0
      have h_2_9 : c2 ≠ c9 := r_10_2_9 t10
      have h_2_12 : c2 ≠ c12 := r_0_2_12 t0
      have h_2_13 : c2 ≠ c13 := p_2_13
      have h_9_12 : c9 ≠ c12 := p_9_12
      have h_9_13 : c9 ≠ c13 := r_10_9_13 t10
      have h_12_13 : c12 ≠ c13 := p_12_13
      simp [h_0_1, h_0_2, h_0_9, h_0_12, h_0_13, h_1_2, h_1_9, h_1_12, h_1_13, h_2_9, h_2_12, h_2_13, h_9_12, h_9_13, h_12_13]
    have hc := List.Nodup.length_le_card hn
    norm_num at hc
  · have hn : [c0, c1, c2, c10, c12, c13].Nodup := by
      have h_0_1 : c0 ≠ c1 := p_0_1
      have h_0_2 : c0 ≠ c2 := p_0_2
      have h_0_10 : c0 ≠ c10 := r_2_0_10 t2
      have h_0_12 : c0 ≠ c12 := p_0_12
      have h_0_13 : c0 ≠ c13 := p_0_13
      have h_1_2 : c1 ≠ c2 := p_1_2
      have h_1_10 : c1 ≠ c10 := r_2_1_10 t2
      have h_1_12 : c1 ≠ c12 := p_1_12
      have h_1_13 : c1 ≠ c13 := r_2_1_13 t2
      have h_2_10 : c2 ≠ c10 := p_2_10
      have h_2_12 : c2 ≠ c12 := r_13_2_12 t13
      have h_2_13 : c2 ≠ c13 := p_2_13
      have h_10_12 : c10 ≠ c12 := r_13_10_12 t13
      have h_10_13 : c10 ≠ c13 := p_10_13
      have h_12_13 : c12 ≠ c13 := p_12_13
      simp [h_0_1, h_0_2, h_0_10, h_0_12, h_0_13, h_1_2, h_1_10, h_1_12, h_1_13, h_2_10, h_2_12, h_2_13, h_10_12, h_10_13, h_12_13]
    have hc := List.Nodup.length_le_card hn
    norm_num at hc
  · have hn : [c0, c1, c2, c10, c12, c13].Nodup := by
      have h_0_1 : c0 ≠ c1 := p_0_1
      have h_0_2 : c0 ≠ c2 := p_0_2
      have h_0_10 : c0 ≠ c10 := r_13_0_10 t13
      have h_0_12 : c0 ≠ c12 := p_0_12
      have h_0_13 : c0 ≠ c13 := p_0_13
      have h_1_2 : c1 ≠ c2 := p_1_2
      have h_1_10 : c1 ≠ c10 := r_9_1_10 t9
      have h_1_12 : c1 ≠ c12 := p_1_12
      have h_1_13 : c1 ≠ c13 := r_0_1_13 t0
      have h_2_10 : c2 ≠ c10 := p_2_10
      have h_2_12 : c2 ≠ c12 := r_0_2_12 t0
      have h_2_13 : c2 ≠ c13 := p_2_13
      have h_10_12 : c10 ≠ c12 := r_9_10_12 t9
      have h_10_13 : c10 ≠ c13 := p_10_13
      have h_12_13 : c12 ≠ c13 := p_12_13
      simp [h_0_1, h_0_2, h_0_10, h_0_12, h_0_13, h_1_2, h_1_10, h_1_12, h_1_13, h_2_10, h_2_12, h_2_13, h_10_12, h_10_13, h_12_13]
    have hc := List.Nodup.length_le_card hn
    norm_num at hc
  · have hn : [c3, c5, c6, c7, c8, c14].Nodup := by
      have h_3_5 : c3 ≠ c5 := p_3_5
      have h_3_6 : c3 ≠ c6 := p_3_6
      have h_3_7 : c3 ≠ c7 := r_4_3_7 t4
      have h_3_8 : c3 ≠ c8 := r_6_3_8 t6
      have h_3_14 : c3 ≠ c14 := p_3_14
      have h_5_6 : c5 ≠ c6 := r_14_5_6 t14
      have h_5_7 : c5 ≠ c7 := r_4_5_7 t4
      have h_5_8 : c5 ≠ c8 := p_5_8
      have h_5_14 : c5 ≠ c14 := p_5_14
      have h_6_7 : c6 ≠ c7 := p_6_7
      have h_6_8 : c6 ≠ c8 := p_6_8
      have h_6_14 : c6 ≠ c14 := p_6_14
      have h_7_8 : c7 ≠ c8 := p_7_8
      have h_7_14 : c7 ≠ c14 := r_6_7_14 t6
      have h_8_14 : c8 ≠ c14 := p_8_14
      simp [h_3_5, h_3_6, h_3_7, h_3_8, h_3_14, h_5_6, h_5_7, h_5_8, h_5_14, h_6_7, h_6_8, h_6_14, h_7_8, h_7_14, h_8_14]
    have hc := List.Nodup.length_le_card hn
    norm_num at hc
  · have hn : [c3, c4, c5, c6, c8, c14].Nodup := by
      have h_3_4 : c3 ≠ c4 := p_3_4
      have h_3_5 : c3 ≠ c5 := p_3_5
      have h_3_6 : c3 ≠ c6 := p_3_6
      have h_3_8 : c3 ≠ c8 := r_14_3_8 t14
      have h_3_14 : c3 ≠ c14 := p_3_14
      have h_4_5 : c4 ≠ c5 := p_4_5
      have h_4_6 : c4 ≠ c6 := r_3_4_6 t3
      have h_4_8 : c4 ≠ c8 := r_7_4_8 t7
      have h_4_14 : c4 ≠ c14 := r_3_4_14 t3
      have h_5_6 : c5 ≠ c6 := r_3_5_6 t3
      have h_5_8 : c5 ≠ c8 := p_5_8
      have h_5_14 : c5 ≠ c14 := p_5_14
      have h_6_8 : c6 ≠ c8 := p_6_8
      have h_6_14 : c6 ≠ c14 := p_6_14
      have h_8_14 : c8 ≠ c14 := p_8_14
      simp [h_3_4, h_3_5, h_3_6, h_3_8, h_3_14, h_4_5, h_4_6, h_4_8, h_4_14, h_5_6, h_5_8, h_5_14, h_6_8, h_6_14, h_8_14]
    have hc := List.Nodup.length_le_card hn
    norm_num at hc
  · have hn : [c3, c4, c5, c6, c8, c14].Nodup := by
      have h_3_4 : c3 ≠ c4 := p_3_4
      have h_3_5 : c3 ≠ c5 := p_3_5
      have h_3_6 : c3 ≠ c6 := p_3_6
      have h_3_8 : c3 ≠ c8 := r_5_3_8 t5
      have h_3_14 : c3 ≠ c14 := p_3_14
      have h_4_5 : c4 ≠ c5 := p_4_5
      have h_4_6 : c4 ≠ c6 := r_7_4_6 t7
      have h_4_8 : c4 ≠ c8 := r_5_4_8 t5
      have h_4_14 : c4 ≠ c14 := r_5_4_14 t5
      have h_5_6 : c5 ≠ c6 := r_14_5_6 t14
      have h_5_8 : c5 ≠ c8 := p_5_8
      have h_5_14 : c5 ≠ c14 := p_5_14
      have h_6_8 : c6 ≠ c8 := p_6_8
      have h_6_14 : c6 ≠ c14 := p_6_14
      have h_8_14 : c8 ≠ c14 := p_8_14
      simp [h_3_4, h_3_5, h_3_6, h_3_8, h_3_14, h_4_5, h_4_6, h_4_8, h_4_14, h_5_6, h_5_8, h_5_14, h_6_8, h_6_14, h_8_14]
    have hc := List.Nodup.length_le_card hn
    norm_num at hc
  · have hn : [c3, c5, c6, c7, c8, c14].Nodup := by
      have h_3_5 : c3 ≠ c5 := p_3_5
      have h_3_6 : c3 ≠ c6 := p_3_6
      have h_3_7 : c3 ≠ c7 := r_4_3_7 t4
      have h_3_8 : c3 ≠ c8 := r_14_3_8 t14
      have h_3_14 : c3 ≠ c14 := p_3_14
      have h_5_6 : c5 ≠ c6 := r_8_5_6 t8
      have h_5_7 : c5 ≠ c7 := r_4_5_7 t4
      have h_5_8 : c5 ≠ c8 := p_5_8
      have h_5_14 : c5 ≠ c14 := p_5_14
      have h_6_7 : c6 ≠ c7 := p_6_7
      have h_6_8 : c6 ≠ c8 := p_6_8
      have h_6_14 : c6 ≠ c14 := p_6_14
      have h_7_8 : c7 ≠ c8 := p_7_8
      have h_7_14 : c7 ≠ c14 := r_8_7_14 t8
      have h_8_14 : c8 ≠ c14 := p_8_14
      simp [h_3_5, h_3_6, h_3_7, h_3_8, h_3_14, h_5_6, h_5_7, h_5_8, h_5_14, h_6_7, h_6_8, h_6_14, h_7_8, h_7_14, h_8_14]
    have hc := List.Nodup.length_le_card hn
    norm_num at hc
