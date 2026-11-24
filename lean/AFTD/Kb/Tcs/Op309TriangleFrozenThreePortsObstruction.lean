import AFTD.Prelude

/-!
# op309_triangle_frozen_three_ports_obstruction

Topic: graphs   Node: 705d1935ea9f

Provenance: helper lemma. OP-309 triangle contraction local boundary obstruction

With fixed port colors 0, 1, 2, any proper coloring of the triangle fails to provide a rich internal neighbor at at least one port, when richness is expressed by the three displayed four-color tests.
-/

theorem op309_triangle_frozen_three_ports_obstruction :
    ∀ a b c : Fin 5,
      a ≠ b → b ≠ c → c ≠ a →
      a ≠ 0 → c ≠ 0 → a ≠ 1 → b ≠ 1 → b ≠ 2 → c ≠ 2 →
      ¬ (([0,1,b,c] : List (Fin 5)).Nodup ∨ ([2,0,a,b] : List (Fin 5)).Nodup) ∨
      ¬ (([0,1,b,c] : List (Fin 5)).Nodup ∨ ([1,2,c,a] : List (Fin 5)).Nodup) ∨
      ¬ (([1,2,c,a] : List (Fin 5)).Nodup ∨ ([2,0,a,b] : List (Fin 5)).Nodup) := by
  intro a b c
  fin_cases a <;> fin_cases b <;> fin_cases c <;> decide
