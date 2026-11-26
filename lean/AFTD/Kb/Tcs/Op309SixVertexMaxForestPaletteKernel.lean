import AFTD.Prelude

/-!
# op309_six_vertex_max_forest_palette_kernel

Topic: graphs   Node: 17d1000bb312

Provenance: helper lemma. OP-309 maximum-forest six-vertex obstruction; compare the six-color pigeonhole proof in op309_triangle_three_distinct_ports_no_two_rich_edges.

Three distinct colors cannot all avoid three other distinct colors in a five-color palette.
-/

theorem op309_six_vertex_max_forest_palette_kernel
  (a b c x y z : Fin 5)
  (hstar : ([a,b,c] : List (Fin 5)).Nodup)
  (hterminal : ([x,y,z] : List (Fin 5)).Nodup)
  (hx : x ≠ a ∧ x ≠ b ∧ x ≠ c)
  (hy : y ≠ a ∧ y ≠ b ∧ y ≠ c)
  (hz : z ≠ a ∧ z ≠ b ∧ z ≠ c) : False := by
  have h6 : ([a,b,c,x,y,z] : List (Fin 5)).Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton,
      List.nodup_singleton, not_or] at *
    aesop
  have hh := h6.length_le_card
  norm_num at hh
