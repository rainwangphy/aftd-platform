import AFTD.Prelude

/-!
# op309_ten_vertex_all_perfect_cut_obstruction_kernel

Topic: graphs   Node: 340555fd243a

Provenance: helper lemma. Finite Boolean core of the ten-vertex matching-cut obstruction in experiments 31285, 31287 and 31288.

For every Boolean assignment to the ten vertices, if the endpoints of one of the six displayed perfect matchings agree, some displayed edge has all its neighboring edges monochromatic.
-/

set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 1000000

theorem op309_ten_vertex_all_perfect_cut_obstruction_kernel :
    ∀ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 : Fin 2,
      ((a0 = a3 ∧ a1 = a6 ∧ a2 = a7 ∧ a4 = a9 ∧ a5 = a8) ∨
      (a0 = a3 ∧ a1 = a8 ∧ a2 = a6 ∧ a4 = a7 ∧ a5 = a9) ∨
      (a0 = a6 ∧ a1 = a4 ∧ a2 = a7 ∧ a3 = a8 ∧ a5 = a9) ∨
      (a0 = a6 ∧ a1 = a8 ∧ a2 = a5 ∧ a3 = a7 ∧ a4 = a9) ∨
      (a0 = a9 ∧ a1 = a4 ∧ a2 = a6 ∧ a3 = a7 ∧ a5 = a8) ∨
      (a0 = a9 ∧ a1 = a6 ∧ a2 = a5 ∧ a3 = a8 ∧ a4 = a7)) →
      ((a0 = a6 ∧ a0 = a9 ∧ a3 = a7 ∧ a3 = a8) ∨
      (a0 = a3 ∧ a0 = a9 ∧ a1 = a6 ∧ a2 = a6) ∨
      (a0 = a3 ∧ a0 = a6 ∧ a4 = a9 ∧ a5 = a9) ∨
      (a1 = a6 ∧ a1 = a8 ∧ a4 = a7 ∧ a4 = a9) ∨
      (a0 = a6 ∧ a1 = a4 ∧ a1 = a8 ∧ a2 = a6) ∨
      (a1 = a4 ∧ a1 = a6 ∧ a3 = a8 ∧ a5 = a8) ∨
      (a2 = a6 ∧ a2 = a7 ∧ a5 = a8 ∧ a5 = a9) ∨
      (a0 = a6 ∧ a1 = a6 ∧ a2 = a5 ∧ a2 = a7) ∨
      (a2 = a5 ∧ a2 = a6 ∧ a3 = a7 ∧ a4 = a7) ∨
      (a0 = a3 ∧ a2 = a7 ∧ a3 = a8 ∧ a4 = a7) ∨
      (a0 = a3 ∧ a1 = a8 ∧ a3 = a7 ∧ a5 = a8) ∨
      (a1 = a4 ∧ a2 = a7 ∧ a3 = a7 ∧ a4 = a9) ∨
      (a0 = a9 ∧ a1 = a4 ∧ a4 = a7 ∧ a5 = a9) ∨
      (a1 = a8 ∧ a2 = a5 ∧ a3 = a8 ∧ a5 = a9) ∨
      (a0 = a9 ∧ a2 = a5 ∧ a4 = a9 ∧ a5 = a8)) := by
  intro a0 a1 a2 a3 a4
  fin_cases a0 <;> fin_cases a1 <;> fin_cases a2 <;> fin_cases a3 <;> fin_cases a4 <;> decide
