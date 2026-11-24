import AFTD.Prelude

/-!
# op309_triangle_spoke_recolor_obstruction_core

Topic: graphs   Node: 5fae6aae2db4

Provenance: helper lemma. OP-309 triangle expansion spoke-only obstruction

The displayed local properness and rich-neighbor constraints cannot all hold with five colors.
-/

set_option maxHeartbeats 1000000

theorem op309_triangle_spoke_recolor_obstruction_core
    (s0 s1 s2 a b c : Fin 5)
    (hs23 : s2 ≠ 3) (hs24 : s2 ≠ 4) (hsc : s2 ≠ c)
    (h3 : ([1,s0,3,0] : List (Fin 5)).Nodup ∨ ([3,4,a,c] : List (Fin 5)).Nodup)
    (h7 : ([3,4,b,c] : List (Fin 5)).Nodup)
    (h9 : ([s0,s2,a,c] : List (Fin 5)).Nodup ∨ ([s1,s2,a,b] : List (Fin 5)).Nodup)
    (h11 : ([2,s0,4,3] : List (Fin 5)).Nodup) : False := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_singleton,
    List.nodup_singleton, not_or, ne_eq] at *
  omega
