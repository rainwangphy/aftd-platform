import AFTD.Prelude

/-!
# op309_triangle_three_distinct_ports_no_two_rich_edges

Topic: graphs   Node: 705c1ad41073

Provenance: helper lemma. OP-309 triangle contraction boundary analysis

For a properly colored triangle with three pairwise distinct port colors, the displayed richness requirements cannot both hold on two incident triangle edges using five colors.
-/

theorem op309_triangle_three_distinct_ports_no_two_rich_edges
    (p0 p1 p2 a b c : Fin 5)
    (hports : ([p0,p1,p2] : List (Fin 5)).Nodup)
    (hproper0 : ([p0,a,c] : List (Fin 5)).Nodup)
    (hproper1 : ([p1,a,b] : List (Fin 5)).Nodup)
    (hproper2 : ([p2,b,c] : List (Fin 5)).Nodup)
    (hrich01 : ([p0,p1,b,c] : List (Fin 5)).Nodup)
    (hrich12 : ([p1,p2,c,a] : List (Fin 5)).Nodup) : False := by
  have h6 : ([p0,p1,p2,a,b,c] : List (Fin 5)).Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton,
      List.nodup_singleton, not_or] at *
    aesop
  have hh := h6.length_le_card
  norm_num at hh
