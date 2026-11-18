import AFTD.Prelude

/-!
# op309_common_neighbor_diamond_rich_port_kernel

Topic: graphs   Node: 585df9dc69b6

Provenance: helper lemma. Finite local obstruction for OP-309, independently enumerated in experiments 31422 and 31423.

After normalizing three incident edge colors to 0, 1, and 2 in the displayed diamond-plus-neighbor configuration, if internal rich edges meet all four diamond vertices, neither edge from a diamond tip to their common external neighbor is rich.
-/

set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

theorem op309_common_neighbor_diamond_rich_port_kernel :
    ∀ c3 c4 c5 c6 c7 : Fin 5,
    let c0 : Fin 5 := 0; let c1 : Fin 5 := 1; let c2 : Fin 5 := 2;
    (c0 ≠ c1 ∧
      c0 ≠ c2 ∧
      c0 ≠ c3 ∧
      c0 ≠ c4 ∧
      c1 ≠ c2 ∧
      c1 ≠ c3 ∧
      c1 ≠ c5 ∧
      c2 ≠ c4 ∧
      c2 ≠ c6 ∧
      c3 ≠ c4 ∧
      c3 ≠ c5 ∧
      c4 ≠ c6 ∧
      c5 ≠ c6 ∧
      c5 ≠ c7 ∧
      c6 ≠ c7) →
    (((c1 ≠ c2 ∧ c1 ≠ c3 ∧ c1 ≠ c4 ∧ c2 ≠ c3 ∧ c2 ≠ c4 ∧ c3 ≠ c4) ∨ (c0 ≠ c2 ∧ c0 ≠ c3 ∧ c0 ≠ c5 ∧ c2 ≠ c3 ∧ c2 ≠ c5 ∧ c3 ≠ c5) ∨ (c0 ≠ c1 ∧ c0 ≠ c4 ∧ c0 ≠ c6 ∧ c1 ≠ c4 ∧ c1 ≠ c6 ∧ c4 ≠ c6)) ∧
      ((c1 ≠ c2 ∧ c1 ≠ c3 ∧ c1 ≠ c4 ∧ c2 ≠ c3 ∧ c2 ≠ c4 ∧ c3 ≠ c4) ∨ (c0 ≠ c1 ∧ c0 ≠ c4 ∧ c0 ≠ c5 ∧ c1 ≠ c4 ∧ c1 ≠ c5 ∧ c4 ≠ c5) ∨ (c0 ≠ c2 ∧ c0 ≠ c3 ∧ c0 ≠ c6 ∧ c2 ≠ c3 ∧ c2 ≠ c6 ∧ c3 ≠ c6)) ∧
      ((c0 ≠ c2 ∧ c0 ≠ c3 ∧ c0 ≠ c5 ∧ c2 ≠ c3 ∧ c2 ≠ c5 ∧ c3 ≠ c5) ∨ (c0 ≠ c1 ∧ c0 ≠ c4 ∧ c0 ≠ c5 ∧ c1 ≠ c4 ∧ c1 ≠ c5 ∧ c4 ≠ c5)) ∧
      ((c0 ≠ c1 ∧ c0 ≠ c4 ∧ c0 ≠ c6 ∧ c1 ≠ c4 ∧ c1 ≠ c6 ∧ c4 ≠ c6) ∨ (c0 ≠ c2 ∧ c0 ≠ c3 ∧ c0 ≠ c6 ∧ c2 ≠ c3 ∧ c2 ≠ c6 ∧ c3 ≠ c6))) →
    ¬ ((c1 ≠ c3 ∧ c1 ≠ c6 ∧ c1 ≠ c7 ∧ c3 ≠ c6 ∧ c3 ≠ c7 ∧ c6 ≠ c7) ∨ (c2 ≠ c4 ∧ c2 ≠ c5 ∧ c2 ≠ c7 ∧ c4 ≠ c5 ∧ c4 ≠ c7 ∧ c5 ≠ c7)) := by
  intro c3 c4 c5 c6 c7
  omega
