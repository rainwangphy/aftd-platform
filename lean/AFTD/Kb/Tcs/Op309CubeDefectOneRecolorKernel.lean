import AFTD.Prelude

/-!
# op309_cube_defect_one_recolor_kernel

Topic: graphs   Node: 3aae1c8f6101

Provenance: helper lemma. Finite kernel for the cube matching-recoloring obstruction of OP-309, experiments 31417 and 31418.

For the displayed normalized four-color assignment on the twelve edges of the eight-vertex graph, replacing any subset by color 4 cannot simultaneously preserve properness and give every edge a rich neighbor.
-/

set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 1000000

theorem op309_cube_defect_one_recolor_kernel :
    ∀ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Fin 2,
    let c0 : Fin 5 := if x0 = 1 then 4 else 0;
    let c1 : Fin 5 := if x1 = 1 then 4 else 1;
    let c2 : Fin 5 := if x2 = 1 then 4 else 2;
    let c3 : Fin 5 := if x3 = 1 then 4 else 1;
    let c4 : Fin 5 := if x4 = 1 then 4 else 0;
    let c5 : Fin 5 := if x5 = 1 then 4 else 2;
    let c6 : Fin 5 := if x6 = 1 then 4 else 3;
    let c7 : Fin 5 := if x7 = 1 then 4 else 0;
    let c8 : Fin 5 := if x8 = 1 then 4 else 1;
    let c9 : Fin 5 := if x9 = 1 then 4 else 3;
    let c10 : Fin 5 := if x10 = 1 then 4 else 1;
    let c11 : Fin 5 := if x11 = 1 then 4 else 0;
    (c0 ≠ c1 ∧
      c0 ≠ c2 ∧
      c0 ≠ c3 ∧
      c0 ≠ c6 ∧
      c1 ≠ c2 ∧
      c1 ≠ c4 ∧
      c1 ≠ c9 ∧
      c2 ≠ c7 ∧
      c2 ≠ c10 ∧
      c3 ≠ c4 ∧
      c3 ≠ c5 ∧
      c3 ≠ c6 ∧
      c4 ≠ c5 ∧
      c4 ≠ c9 ∧
      c5 ≠ c8 ∧
      c5 ≠ c11 ∧
      c6 ≠ c7 ∧
      c6 ≠ c8 ∧
      c7 ≠ c8 ∧
      c7 ≠ c10 ∧
      c8 ≠ c11 ∧
      c9 ≠ c10 ∧
      c9 ≠ c11 ∧
      c10 ≠ c11) → ¬
    (((c0 ≠ c2 ∧ c0 ≠ c4 ∧ c0 ≠ c9 ∧ c2 ≠ c4 ∧ c2 ≠ c9 ∧ c4 ≠ c9) ∨ (c0 ≠ c1 ∧ c0 ≠ c7 ∧ c0 ≠ c10 ∧ c1 ≠ c7 ∧ c1 ≠ c10 ∧ c7 ≠ c10) ∨ (c0 ≠ c4 ∧ c0 ≠ c5 ∧ c0 ≠ c6 ∧ c4 ≠ c5 ∧ c4 ≠ c6 ∧ c5 ≠ c6) ∨ (c0 ≠ c3 ∧ c0 ≠ c7 ∧ c0 ≠ c8 ∧ c3 ≠ c7 ∧ c3 ≠ c8 ∧ c7 ≠ c8)) ∧
      ((c1 ≠ c2 ∧ c1 ≠ c3 ∧ c1 ≠ c6 ∧ c2 ≠ c3 ∧ c2 ≠ c6 ∧ c3 ≠ c6) ∨ (c0 ≠ c1 ∧ c0 ≠ c7 ∧ c0 ≠ c10 ∧ c1 ≠ c7 ∧ c1 ≠ c10 ∧ c7 ≠ c10) ∨ (c1 ≠ c3 ∧ c1 ≠ c5 ∧ c1 ≠ c9 ∧ c3 ≠ c5 ∧ c3 ≠ c9 ∧ c5 ≠ c9) ∨ (c1 ≠ c4 ∧ c1 ≠ c10 ∧ c1 ≠ c11 ∧ c4 ≠ c10 ∧ c4 ≠ c11 ∧ c10 ≠ c11)) ∧
      ((c1 ≠ c2 ∧ c1 ≠ c3 ∧ c1 ≠ c6 ∧ c2 ≠ c3 ∧ c2 ≠ c6 ∧ c3 ≠ c6) ∨ (c0 ≠ c2 ∧ c0 ≠ c4 ∧ c0 ≠ c9 ∧ c2 ≠ c4 ∧ c2 ≠ c9 ∧ c4 ≠ c9) ∨ (c2 ≠ c6 ∧ c2 ≠ c8 ∧ c2 ≠ c10 ∧ c6 ≠ c8 ∧ c6 ≠ c10 ∧ c8 ≠ c10) ∨ (c2 ≠ c7 ∧ c2 ≠ c9 ∧ c2 ≠ c11 ∧ c7 ≠ c9 ∧ c7 ≠ c11 ∧ c9 ≠ c11)) ∧
      ((c1 ≠ c2 ∧ c1 ≠ c3 ∧ c1 ≠ c6 ∧ c2 ≠ c3 ∧ c2 ≠ c6 ∧ c3 ≠ c6) ∨ (c1 ≠ c3 ∧ c1 ≠ c5 ∧ c1 ≠ c9 ∧ c3 ≠ c5 ∧ c3 ≠ c9 ∧ c5 ≠ c9) ∨ (c3 ≠ c4 ∧ c3 ≠ c8 ∧ c3 ≠ c11 ∧ c4 ≠ c8 ∧ c4 ≠ c11 ∧ c8 ≠ c11) ∨ (c0 ≠ c3 ∧ c0 ≠ c7 ∧ c0 ≠ c8 ∧ c3 ≠ c7 ∧ c3 ≠ c8 ∧ c7 ≠ c8)) ∧
      ((c0 ≠ c2 ∧ c0 ≠ c4 ∧ c0 ≠ c9 ∧ c2 ≠ c4 ∧ c2 ≠ c9 ∧ c4 ≠ c9) ∨ (c0 ≠ c4 ∧ c0 ≠ c5 ∧ c0 ≠ c6 ∧ c4 ≠ c5 ∧ c4 ≠ c6 ∧ c5 ≠ c6) ∨ (c3 ≠ c4 ∧ c3 ≠ c8 ∧ c3 ≠ c11 ∧ c4 ≠ c8 ∧ c4 ≠ c11 ∧ c8 ≠ c11) ∨ (c1 ≠ c4 ∧ c1 ≠ c10 ∧ c1 ≠ c11 ∧ c4 ≠ c10 ∧ c4 ≠ c11 ∧ c10 ≠ c11)) ∧
      ((c0 ≠ c4 ∧ c0 ≠ c5 ∧ c0 ≠ c6 ∧ c4 ≠ c5 ∧ c4 ≠ c6 ∧ c5 ≠ c6) ∨ (c1 ≠ c3 ∧ c1 ≠ c5 ∧ c1 ≠ c9 ∧ c3 ≠ c5 ∧ c3 ≠ c9 ∧ c5 ≠ c9) ∨ (c5 ≠ c6 ∧ c5 ≠ c7 ∧ c5 ≠ c11 ∧ c6 ≠ c7 ∧ c6 ≠ c11 ∧ c7 ≠ c11) ∨ (c5 ≠ c8 ∧ c5 ≠ c9 ∧ c5 ≠ c10 ∧ c8 ≠ c9 ∧ c8 ≠ c10 ∧ c9 ≠ c10)) ∧
      ((c1 ≠ c2 ∧ c1 ≠ c3 ∧ c1 ≠ c6 ∧ c2 ≠ c3 ∧ c2 ≠ c6 ∧ c3 ≠ c6) ∨ (c0 ≠ c4 ∧ c0 ≠ c5 ∧ c0 ≠ c6 ∧ c4 ≠ c5 ∧ c4 ≠ c6 ∧ c5 ≠ c6) ∨ (c2 ≠ c6 ∧ c2 ≠ c8 ∧ c2 ≠ c10 ∧ c6 ≠ c8 ∧ c6 ≠ c10 ∧ c8 ≠ c10) ∨ (c5 ≠ c6 ∧ c5 ≠ c7 ∧ c5 ≠ c11 ∧ c6 ≠ c7 ∧ c6 ≠ c11 ∧ c7 ≠ c11)) ∧
      ((c0 ≠ c1 ∧ c0 ≠ c7 ∧ c0 ≠ c10 ∧ c1 ≠ c7 ∧ c1 ≠ c10 ∧ c7 ≠ c10) ∨ (c0 ≠ c3 ∧ c0 ≠ c7 ∧ c0 ≠ c8 ∧ c3 ≠ c7 ∧ c3 ≠ c8 ∧ c7 ≠ c8) ∨ (c5 ≠ c6 ∧ c5 ≠ c7 ∧ c5 ≠ c11 ∧ c6 ≠ c7 ∧ c6 ≠ c11 ∧ c7 ≠ c11) ∨ (c2 ≠ c7 ∧ c2 ≠ c9 ∧ c2 ≠ c11 ∧ c7 ≠ c9 ∧ c7 ≠ c11 ∧ c9 ≠ c11)) ∧
      ((c3 ≠ c4 ∧ c3 ≠ c8 ∧ c3 ≠ c11 ∧ c4 ≠ c8 ∧ c4 ≠ c11 ∧ c8 ≠ c11) ∨ (c0 ≠ c3 ∧ c0 ≠ c7 ∧ c0 ≠ c8 ∧ c3 ≠ c7 ∧ c3 ≠ c8 ∧ c7 ≠ c8) ∨ (c2 ≠ c6 ∧ c2 ≠ c8 ∧ c2 ≠ c10 ∧ c6 ≠ c8 ∧ c6 ≠ c10 ∧ c8 ≠ c10) ∨ (c5 ≠ c8 ∧ c5 ≠ c9 ∧ c5 ≠ c10 ∧ c8 ≠ c9 ∧ c8 ≠ c10 ∧ c9 ≠ c10)) ∧
      ((c0 ≠ c2 ∧ c0 ≠ c4 ∧ c0 ≠ c9 ∧ c2 ≠ c4 ∧ c2 ≠ c9 ∧ c4 ≠ c9) ∨ (c1 ≠ c3 ∧ c1 ≠ c5 ∧ c1 ≠ c9 ∧ c3 ≠ c5 ∧ c3 ≠ c9 ∧ c5 ≠ c9) ∨ (c2 ≠ c7 ∧ c2 ≠ c9 ∧ c2 ≠ c11 ∧ c7 ≠ c9 ∧ c7 ≠ c11 ∧ c9 ≠ c11) ∨ (c5 ≠ c8 ∧ c5 ≠ c9 ∧ c5 ≠ c10 ∧ c8 ≠ c9 ∧ c8 ≠ c10 ∧ c9 ≠ c10)) ∧
      ((c0 ≠ c1 ∧ c0 ≠ c7 ∧ c0 ≠ c10 ∧ c1 ≠ c7 ∧ c1 ≠ c10 ∧ c7 ≠ c10) ∨ (c2 ≠ c6 ∧ c2 ≠ c8 ∧ c2 ≠ c10 ∧ c6 ≠ c8 ∧ c6 ≠ c10 ∧ c8 ≠ c10) ∨ (c1 ≠ c4 ∧ c1 ≠ c10 ∧ c1 ≠ c11 ∧ c4 ≠ c10 ∧ c4 ≠ c11 ∧ c10 ≠ c11) ∨ (c5 ≠ c8 ∧ c5 ≠ c9 ∧ c5 ≠ c10 ∧ c8 ≠ c9 ∧ c8 ≠ c10 ∧ c9 ≠ c10)) ∧
      ((c3 ≠ c4 ∧ c3 ≠ c8 ∧ c3 ≠ c11 ∧ c4 ≠ c8 ∧ c4 ≠ c11 ∧ c8 ≠ c11) ∨ (c5 ≠ c6 ∧ c5 ≠ c7 ∧ c5 ≠ c11 ∧ c6 ≠ c7 ∧ c6 ≠ c11 ∧ c7 ≠ c11) ∨ (c1 ≠ c4 ∧ c1 ≠ c10 ∧ c1 ≠ c11 ∧ c4 ≠ c10 ∧ c4 ≠ c11 ∧ c10 ≠ c11) ∨ (c2 ≠ c7 ∧ c2 ≠ c9 ∧ c2 ≠ c11 ∧ c7 ≠ c9 ∧ c7 ≠ c11 ∧ c9 ≠ c11))) := by
  intro x0 x1 x2 x3 x4 x5
  fin_cases x0 <;> fin_cases x1 <;> fin_cases x2 <;> fin_cases x3 <;> fin_cases x4 <;> fin_cases x5 <;> decide
