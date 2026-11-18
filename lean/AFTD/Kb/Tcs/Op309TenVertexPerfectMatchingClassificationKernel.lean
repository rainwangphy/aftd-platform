import AFTD.Prelude

/-!
# op309_ten_vertex_perfect_matching_classification_kernel

Topic: graphs   Node: f4c04e78acec

Provenance: helper lemma. Finite enumeration of the six perfect matchings of the ten-vertex graph in experiment 31287.

If each of the ten displayed incidence triples contains exactly one selected edge, the selection contains one of the six displayed perfect matchings.
-/

set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 1000000

theorem op309_ten_vertex_perfect_matching_classification_kernel :
    ∀ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 : Fin 2,
    (((x0 = 1 ∧ x1 = 0 ∧ x2 = 0) ∨ (x0 = 0 ∧ x1 = 1 ∧ x2 = 0) ∨ (x0 = 0 ∧ x1 = 0 ∧ x2 = 1)) ∧
      ((x3 = 1 ∧ x4 = 0 ∧ x5 = 0) ∨ (x3 = 0 ∧ x4 = 1 ∧ x5 = 0) ∨ (x3 = 0 ∧ x4 = 0 ∧ x5 = 1)) ∧
      ((x6 = 1 ∧ x7 = 0 ∧ x8 = 0) ∨ (x6 = 0 ∧ x7 = 1 ∧ x8 = 0) ∨ (x6 = 0 ∧ x7 = 0 ∧ x8 = 1)) ∧
      ((x0 = 1 ∧ x9 = 0 ∧ x10 = 0) ∨ (x0 = 0 ∧ x9 = 1 ∧ x10 = 0) ∨ (x0 = 0 ∧ x9 = 0 ∧ x10 = 1)) ∧
      ((x3 = 1 ∧ x11 = 0 ∧ x12 = 0) ∨ (x3 = 0 ∧ x11 = 1 ∧ x12 = 0) ∨ (x3 = 0 ∧ x11 = 0 ∧ x12 = 1)) ∧
      ((x6 = 1 ∧ x13 = 0 ∧ x14 = 0) ∨ (x6 = 0 ∧ x13 = 1 ∧ x14 = 0) ∨ (x6 = 0 ∧ x13 = 0 ∧ x14 = 1)) ∧
      ((x1 = 1 ∧ x4 = 0 ∧ x7 = 0) ∨ (x1 = 0 ∧ x4 = 1 ∧ x7 = 0) ∨ (x1 = 0 ∧ x4 = 0 ∧ x7 = 1)) ∧
      ((x8 = 1 ∧ x9 = 0 ∧ x11 = 0) ∨ (x8 = 0 ∧ x9 = 1 ∧ x11 = 0) ∨ (x8 = 0 ∧ x9 = 0 ∧ x11 = 1)) ∧
      ((x5 = 1 ∧ x10 = 0 ∧ x13 = 0) ∨ (x5 = 0 ∧ x10 = 1 ∧ x13 = 0) ∨ (x5 = 0 ∧ x10 = 0 ∧ x13 = 1)) ∧
      ((x2 = 1 ∧ x12 = 0 ∧ x14 = 0) ∨ (x2 = 0 ∧ x12 = 1 ∧ x14 = 0) ∨ (x2 = 0 ∧ x12 = 0 ∧ x14 = 1))) →
    ((x0 = 1 ∧ x4 = 1 ∧ x8 = 1 ∧ x12 = 1 ∧ x13 = 1) ∨
      (x0 = 1 ∧ x5 = 1 ∧ x7 = 1 ∧ x11 = 1 ∧ x14 = 1) ∨
      (x1 = 1 ∧ x3 = 1 ∧ x8 = 1 ∧ x10 = 1 ∧ x14 = 1) ∨
      (x1 = 1 ∧ x5 = 1 ∧ x6 = 1 ∧ x9 = 1 ∧ x12 = 1) ∨
      (x2 = 1 ∧ x3 = 1 ∧ x7 = 1 ∧ x9 = 1 ∧ x13 = 1) ∨
      (x2 = 1 ∧ x4 = 1 ∧ x6 = 1 ∧ x10 = 1 ∧ x11 = 1)) := by
  intro x0 x1 x2 x3 x4
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;> fin_cases x4 <;> decide
