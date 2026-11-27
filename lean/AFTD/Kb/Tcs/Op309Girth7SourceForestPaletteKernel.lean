import AFTD.Prelude

/-!
# op309_girth7_source_forest_palette_kernel

Topic: graphs   Node: 0c7487022a23

Provenance: helper lemma. OP-309 girth-seven source-forest quotient; experiment 42311.

The ten-class conflict graph extracted from the girth-seven source-forest quotient is not five-colorable.
-/

theorem op309_girth7_source_forest_palette_kernel (c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 : Fin 5)
    (h0_1 : c0 ≠ c1)
    (h0_3 : c0 ≠ c3)
    (h0_5 : c0 ≠ c5)
    (h0_8 : c0 ≠ c8)
    (h0_9 : c0 ≠ c9)
    (h1_2 : c1 ≠ c2)
    (h1_3 : c1 ≠ c3)
    (h1_4 : c1 ≠ c4)
    (h1_5 : c1 ≠ c5)
    (h1_6 : c1 ≠ c6)
    (h1_7 : c1 ≠ c7)
    (h1_8 : c1 ≠ c8)
    (h1_9 : c1 ≠ c9)
    (h2_4 : c2 ≠ c4)
    (h2_5 : c2 ≠ c5)
    (h2_6 : c2 ≠ c6)
    (h2_7 : c2 ≠ c7)
    (h3_5 : c3 ≠ c5)
    (h3_8 : c3 ≠ c8)
    (h3_9 : c3 ≠ c9)
    (h4_5 : c4 ≠ c5)
    (h4_6 : c4 ≠ c6)
    (h4_7 : c4 ≠ c7)
    (h5_6 : c5 ≠ c6)
    (h5_9 : c5 ≠ c9)
    (h6_7 : c6 ≠ c7)
    (h7_8 : c7 ≠ c8)
    (h8_9 : c8 ≠ c9) : False := by
  have h58 : c5 = c8 := by
    by_contra h58ne
    have hn : [c0, c1, c3, c8, c9, c5].Nodup := by
      have k0_1 : c0 ≠ c1 := h0_1
      have k0_3 : c0 ≠ c3 := h0_3
      have k0_8 : c0 ≠ c8 := h0_8
      have k0_9 : c0 ≠ c9 := h0_9
      have k0_5 : c0 ≠ c5 := h0_5
      have k1_3 : c1 ≠ c3 := h1_3
      have k1_8 : c1 ≠ c8 := h1_8
      have k1_9 : c1 ≠ c9 := h1_9
      have k1_5 : c1 ≠ c5 := h1_5
      have k3_8 : c3 ≠ c8 := h3_8
      have k3_9 : c3 ≠ c9 := h3_9
      have k3_5 : c3 ≠ c5 := h3_5
      have k8_9 : c8 ≠ c9 := h8_9
      have k8_5 : c8 ≠ c5 := Ne.symm h58ne
      have k9_5 : c9 ≠ c5 := Ne.symm h5_9
      simp [k0_1, k0_3, k0_8, k0_9, k0_5, k1_3, k1_8, k1_9, k1_5, k3_8, k3_9, k3_5, k8_9, k8_5, k9_5]
    have hc := List.Nodup.length_le_card hn
    norm_num at hc
  have h57 : c5 ≠ c7 := by
    rw [h58]
    exact Ne.symm h7_8
  have hn : [c1, c5, c2, c4, c6, c7].Nodup := by
      have k1_5 : c1 ≠ c5 := h1_5
      have k1_2 : c1 ≠ c2 := h1_2
      have k1_4 : c1 ≠ c4 := h1_4
      have k1_6 : c1 ≠ c6 := h1_6
      have k1_7 : c1 ≠ c7 := h1_7
      have k5_2 : c5 ≠ c2 := Ne.symm h2_5
      have k5_4 : c5 ≠ c4 := Ne.symm h4_5
      have k5_6 : c5 ≠ c6 := h5_6
      have k5_7 : c5 ≠ c7 := h57
      have k2_4 : c2 ≠ c4 := h2_4
      have k2_6 : c2 ≠ c6 := h2_6
      have k2_7 : c2 ≠ c7 := h2_7
      have k4_6 : c4 ≠ c6 := h4_6
      have k4_7 : c4 ≠ c7 := h4_7
      have k6_7 : c6 ≠ c7 := h6_7
      simp [k1_5, k1_2, k1_4, k1_6, k1_7, k5_2, k5_4, k5_6, k5_7, k2_4, k2_6, k2_7, k4_6, k4_7, k6_7]
  have hc := List.Nodup.length_le_card hn
  norm_num at hc
