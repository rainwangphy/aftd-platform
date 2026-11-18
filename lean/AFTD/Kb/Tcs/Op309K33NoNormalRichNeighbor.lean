import AFTD.Prelude
import AFTD.Kb.Tcs.Op309K33TwoRichImpossibleKernel

/-!
# op309_k33_no_normal_rich_neighbor

Topic: graphs   Node: 63114ad270a7

Provenance: helper lemma. Finite obstruction to a normal-coloring strengthening of OP-309, experiment 30841.

No proper five-edge-coloring of K3,3 is both normal and rich-neighbor.
-/

set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 1000000

theorem op309_k33_normalized_normal_rich_neighbor_impossible :
  ∀ a10 a11 a12 a20 a21 a22 : Fin 5,
  (((0 : Fin 5) ≠ (1 : Fin 5) ∧ (0 : Fin 5) ≠ (2 : Fin 5) ∧ (1 : Fin 5) ≠ (2 : Fin 5)) ∧
    (a10 ≠ a11 ∧ a10 ≠ a12 ∧ a11 ≠ a12) ∧
    (a20 ≠ a21 ∧ a20 ≠ a22 ∧ a21 ≠ a22) ∧
    ((0 : Fin 5) ≠ a10 ∧ (0 : Fin 5) ≠ a20 ∧ a10 ≠ a20) ∧
    ((1 : Fin 5) ≠ a11 ∧ (1 : Fin 5) ≠ a21 ∧ a11 ≠ a21) ∧
    ((2 : Fin 5) ≠ a12 ∧ (2 : Fin 5) ≠ a22 ∧ a12 ≠ a22)) →
  ((((1 : Fin 5) ≠ (2 : Fin 5) ∧ (1 : Fin 5) ≠ a10 ∧ (1 : Fin 5) ≠ a20 ∧ (2 : Fin 5) ≠ a10 ∧ (2 : Fin 5) ≠ a20 ∧ a10 ≠ a20) ∨ (((1 : Fin 5) = a10 ∧ (2 : Fin 5) = a20) ∨ ((1 : Fin 5) = a20 ∧ (2 : Fin 5) = a10))) ∧
    (((0 : Fin 5) ≠ (2 : Fin 5) ∧ (0 : Fin 5) ≠ a11 ∧ (0 : Fin 5) ≠ a21 ∧ (2 : Fin 5) ≠ a11 ∧ (2 : Fin 5) ≠ a21 ∧ a11 ≠ a21) ∨ (((0 : Fin 5) = a11 ∧ (2 : Fin 5) = a21) ∨ ((0 : Fin 5) = a21 ∧ (2 : Fin 5) = a11))) ∧
    (((0 : Fin 5) ≠ (1 : Fin 5) ∧ (0 : Fin 5) ≠ a12 ∧ (0 : Fin 5) ≠ a22 ∧ (1 : Fin 5) ≠ a12 ∧ (1 : Fin 5) ≠ a22 ∧ a12 ≠ a22) ∨ (((0 : Fin 5) = a12 ∧ (1 : Fin 5) = a22) ∨ ((0 : Fin 5) = a22 ∧ (1 : Fin 5) = a12))) ∧
    ((a11 ≠ a12 ∧ a11 ≠ (0 : Fin 5) ∧ a11 ≠ a20 ∧ a12 ≠ (0 : Fin 5) ∧ a12 ≠ a20 ∧ (0 : Fin 5) ≠ a20) ∨ ((a11 = (0 : Fin 5) ∧ a12 = a20) ∨ (a11 = a20 ∧ a12 = (0 : Fin 5)))) ∧
    ((a10 ≠ a12 ∧ a10 ≠ (1 : Fin 5) ∧ a10 ≠ a21 ∧ a12 ≠ (1 : Fin 5) ∧ a12 ≠ a21 ∧ (1 : Fin 5) ≠ a21) ∨ ((a10 = (1 : Fin 5) ∧ a12 = a21) ∨ (a10 = a21 ∧ a12 = (1 : Fin 5)))) ∧
    ((a10 ≠ a11 ∧ a10 ≠ (2 : Fin 5) ∧ a10 ≠ a22 ∧ a11 ≠ (2 : Fin 5) ∧ a11 ≠ a22 ∧ (2 : Fin 5) ≠ a22) ∨ ((a10 = (2 : Fin 5) ∧ a11 = a22) ∨ (a10 = a22 ∧ a11 = (2 : Fin 5)))) ∧
    ((a21 ≠ a22 ∧ a21 ≠ (0 : Fin 5) ∧ a21 ≠ a10 ∧ a22 ≠ (0 : Fin 5) ∧ a22 ≠ a10 ∧ (0 : Fin 5) ≠ a10) ∨ ((a21 = (0 : Fin 5) ∧ a22 = a10) ∨ (a21 = a10 ∧ a22 = (0 : Fin 5)))) ∧
    ((a20 ≠ a22 ∧ a20 ≠ (1 : Fin 5) ∧ a20 ≠ a11 ∧ a22 ≠ (1 : Fin 5) ∧ a22 ≠ a11 ∧ (1 : Fin 5) ≠ a11) ∨ ((a20 = (1 : Fin 5) ∧ a22 = a11) ∨ (a20 = a11 ∧ a22 = (1 : Fin 5)))) ∧
    ((a20 ≠ a21 ∧ a20 ≠ (2 : Fin 5) ∧ a20 ≠ a12 ∧ a21 ≠ (2 : Fin 5) ∧ a21 ≠ a12 ∧ (2 : Fin 5) ≠ a12) ∨ ((a20 = (2 : Fin 5) ∧ a21 = a12) ∨ (a20 = a12 ∧ a21 = (2 : Fin 5))))) →
  ((((0 : Fin 5) ≠ (2 : Fin 5) ∧ (0 : Fin 5) ≠ a11 ∧ (0 : Fin 5) ≠ a21 ∧ (2 : Fin 5) ≠ a11 ∧ (2 : Fin 5) ≠ a21 ∧ a11 ≠ a21) ∨ ((0 : Fin 5) ≠ (1 : Fin 5) ∧ (0 : Fin 5) ≠ a12 ∧ (0 : Fin 5) ≠ a22 ∧ (1 : Fin 5) ≠ a12 ∧ (1 : Fin 5) ≠ a22 ∧ a12 ≠ a22) ∨ (a11 ≠ a12 ∧ a11 ≠ (0 : Fin 5) ∧ a11 ≠ a20 ∧ a12 ≠ (0 : Fin 5) ∧ a12 ≠ a20 ∧ (0 : Fin 5) ≠ a20) ∨ (a21 ≠ a22 ∧ a21 ≠ (0 : Fin 5) ∧ a21 ≠ a10 ∧ a22 ≠ (0 : Fin 5) ∧ a22 ≠ a10 ∧ (0 : Fin 5) ≠ a10)) ∧
    (((1 : Fin 5) ≠ (2 : Fin 5) ∧ (1 : Fin 5) ≠ a10 ∧ (1 : Fin 5) ≠ a20 ∧ (2 : Fin 5) ≠ a10 ∧ (2 : Fin 5) ≠ a20 ∧ a10 ≠ a20) ∨ ((0 : Fin 5) ≠ (1 : Fin 5) ∧ (0 : Fin 5) ≠ a12 ∧ (0 : Fin 5) ≠ a22 ∧ (1 : Fin 5) ≠ a12 ∧ (1 : Fin 5) ≠ a22 ∧ a12 ≠ a22) ∨ (a10 ≠ a12 ∧ a10 ≠ (1 : Fin 5) ∧ a10 ≠ a21 ∧ a12 ≠ (1 : Fin 5) ∧ a12 ≠ a21 ∧ (1 : Fin 5) ≠ a21) ∨ (a20 ≠ a22 ∧ a20 ≠ (1 : Fin 5) ∧ a20 ≠ a11 ∧ a22 ≠ (1 : Fin 5) ∧ a22 ≠ a11 ∧ (1 : Fin 5) ≠ a11)) ∧
    (((1 : Fin 5) ≠ (2 : Fin 5) ∧ (1 : Fin 5) ≠ a10 ∧ (1 : Fin 5) ≠ a20 ∧ (2 : Fin 5) ≠ a10 ∧ (2 : Fin 5) ≠ a20 ∧ a10 ≠ a20) ∨ ((0 : Fin 5) ≠ (2 : Fin 5) ∧ (0 : Fin 5) ≠ a11 ∧ (0 : Fin 5) ≠ a21 ∧ (2 : Fin 5) ≠ a11 ∧ (2 : Fin 5) ≠ a21 ∧ a11 ≠ a21) ∨ (a10 ≠ a11 ∧ a10 ≠ (2 : Fin 5) ∧ a10 ≠ a22 ∧ a11 ≠ (2 : Fin 5) ∧ a11 ≠ a22 ∧ (2 : Fin 5) ≠ a22) ∨ (a20 ≠ a21 ∧ a20 ≠ (2 : Fin 5) ∧ a20 ≠ a12 ∧ a21 ≠ (2 : Fin 5) ∧ a21 ≠ a12 ∧ (2 : Fin 5) ≠ a12)) ∧
    ((a10 ≠ a12 ∧ a10 ≠ (1 : Fin 5) ∧ a10 ≠ a21 ∧ a12 ≠ (1 : Fin 5) ∧ a12 ≠ a21 ∧ (1 : Fin 5) ≠ a21) ∨ (a10 ≠ a11 ∧ a10 ≠ (2 : Fin 5) ∧ a10 ≠ a22 ∧ a11 ≠ (2 : Fin 5) ∧ a11 ≠ a22 ∧ (2 : Fin 5) ≠ a22) ∨ ((1 : Fin 5) ≠ (2 : Fin 5) ∧ (1 : Fin 5) ≠ a10 ∧ (1 : Fin 5) ≠ a20 ∧ (2 : Fin 5) ≠ a10 ∧ (2 : Fin 5) ≠ a20 ∧ a10 ≠ a20) ∨ (a21 ≠ a22 ∧ a21 ≠ (0 : Fin 5) ∧ a21 ≠ a10 ∧ a22 ≠ (0 : Fin 5) ∧ a22 ≠ a10 ∧ (0 : Fin 5) ≠ a10)) ∧
    ((a11 ≠ a12 ∧ a11 ≠ (0 : Fin 5) ∧ a11 ≠ a20 ∧ a12 ≠ (0 : Fin 5) ∧ a12 ≠ a20 ∧ (0 : Fin 5) ≠ a20) ∨ (a10 ≠ a11 ∧ a10 ≠ (2 : Fin 5) ∧ a10 ≠ a22 ∧ a11 ≠ (2 : Fin 5) ∧ a11 ≠ a22 ∧ (2 : Fin 5) ≠ a22) ∨ ((0 : Fin 5) ≠ (2 : Fin 5) ∧ (0 : Fin 5) ≠ a11 ∧ (0 : Fin 5) ≠ a21 ∧ (2 : Fin 5) ≠ a11 ∧ (2 : Fin 5) ≠ a21 ∧ a11 ≠ a21) ∨ (a20 ≠ a22 ∧ a20 ≠ (1 : Fin 5) ∧ a20 ≠ a11 ∧ a22 ≠ (1 : Fin 5) ∧ a22 ≠ a11 ∧ (1 : Fin 5) ≠ a11)) ∧
    ((a11 ≠ a12 ∧ a11 ≠ (0 : Fin 5) ∧ a11 ≠ a20 ∧ a12 ≠ (0 : Fin 5) ∧ a12 ≠ a20 ∧ (0 : Fin 5) ≠ a20) ∨ (a10 ≠ a12 ∧ a10 ≠ (1 : Fin 5) ∧ a10 ≠ a21 ∧ a12 ≠ (1 : Fin 5) ∧ a12 ≠ a21 ∧ (1 : Fin 5) ≠ a21) ∨ ((0 : Fin 5) ≠ (1 : Fin 5) ∧ (0 : Fin 5) ≠ a12 ∧ (0 : Fin 5) ≠ a22 ∧ (1 : Fin 5) ≠ a12 ∧ (1 : Fin 5) ≠ a22 ∧ a12 ≠ a22) ∨ (a20 ≠ a21 ∧ a20 ≠ (2 : Fin 5) ∧ a20 ≠ a12 ∧ a21 ≠ (2 : Fin 5) ∧ a21 ≠ a12 ∧ (2 : Fin 5) ≠ a12)) ∧
    ((a20 ≠ a22 ∧ a20 ≠ (1 : Fin 5) ∧ a20 ≠ a11 ∧ a22 ≠ (1 : Fin 5) ∧ a22 ≠ a11 ∧ (1 : Fin 5) ≠ a11) ∨ (a20 ≠ a21 ∧ a20 ≠ (2 : Fin 5) ∧ a20 ≠ a12 ∧ a21 ≠ (2 : Fin 5) ∧ a21 ≠ a12 ∧ (2 : Fin 5) ≠ a12) ∨ ((1 : Fin 5) ≠ (2 : Fin 5) ∧ (1 : Fin 5) ≠ a10 ∧ (1 : Fin 5) ≠ a20 ∧ (2 : Fin 5) ≠ a10 ∧ (2 : Fin 5) ≠ a20 ∧ a10 ≠ a20) ∨ (a11 ≠ a12 ∧ a11 ≠ (0 : Fin 5) ∧ a11 ≠ a20 ∧ a12 ≠ (0 : Fin 5) ∧ a12 ≠ a20 ∧ (0 : Fin 5) ≠ a20)) ∧
    ((a21 ≠ a22 ∧ a21 ≠ (0 : Fin 5) ∧ a21 ≠ a10 ∧ a22 ≠ (0 : Fin 5) ∧ a22 ≠ a10 ∧ (0 : Fin 5) ≠ a10) ∨ (a20 ≠ a21 ∧ a20 ≠ (2 : Fin 5) ∧ a20 ≠ a12 ∧ a21 ≠ (2 : Fin 5) ∧ a21 ≠ a12 ∧ (2 : Fin 5) ≠ a12) ∨ ((0 : Fin 5) ≠ (2 : Fin 5) ∧ (0 : Fin 5) ≠ a11 ∧ (0 : Fin 5) ≠ a21 ∧ (2 : Fin 5) ≠ a11 ∧ (2 : Fin 5) ≠ a21 ∧ a11 ≠ a21) ∨ (a10 ≠ a12 ∧ a10 ≠ (1 : Fin 5) ∧ a10 ≠ a21 ∧ a12 ≠ (1 : Fin 5) ∧ a12 ≠ a21 ∧ (1 : Fin 5) ≠ a21)) ∧
    ((a21 ≠ a22 ∧ a21 ≠ (0 : Fin 5) ∧ a21 ≠ a10 ∧ a22 ≠ (0 : Fin 5) ∧ a22 ≠ a10 ∧ (0 : Fin 5) ≠ a10) ∨ (a20 ≠ a22 ∧ a20 ≠ (1 : Fin 5) ∧ a20 ≠ a11 ∧ a22 ≠ (1 : Fin 5) ∧ a22 ≠ a11 ∧ (1 : Fin 5) ≠ a11) ∨ ((0 : Fin 5) ≠ (1 : Fin 5) ∧ (0 : Fin 5) ≠ a12 ∧ (0 : Fin 5) ≠ a22 ∧ (1 : Fin 5) ≠ a12 ∧ (1 : Fin 5) ≠ a22 ∧ a12 ≠ a22) ∨ (a10 ≠ a11 ∧ a10 ≠ (2 : Fin 5) ∧ a10 ≠ a22 ∧ a11 ≠ (2 : Fin 5) ∧ a11 ≠ a22 ∧ (2 : Fin 5) ≠ a22))) → False := by
  intro a10 a11
  fin_cases a10 <;> fin_cases a11 <;> decide

theorem op309_k33_no_normal_rich_neighbor (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Fin 5)
  (hproper : (a00 ≠ a01 ∧ a00 ≠ a02 ∧ a01 ≠ a02) ∧
    (a10 ≠ a11 ∧ a10 ≠ a12 ∧ a11 ≠ a12) ∧
    (a20 ≠ a21 ∧ a20 ≠ a22 ∧ a21 ≠ a22) ∧
    (a00 ≠ a10 ∧ a00 ≠ a20 ∧ a10 ≠ a20) ∧
    (a01 ≠ a11 ∧ a01 ≠ a21 ∧ a11 ≠ a21) ∧
    (a02 ≠ a12 ∧ a02 ≠ a22 ∧ a12 ≠ a22))
  (hnormal : ((a01 ≠ a02 ∧ a01 ≠ a10 ∧ a01 ≠ a20 ∧ a02 ≠ a10 ∧ a02 ≠ a20 ∧ a10 ≠ a20) ∨ ((a01 = a10 ∧ a02 = a20) ∨ (a01 = a20 ∧ a02 = a10))) ∧
    ((a00 ≠ a02 ∧ a00 ≠ a11 ∧ a00 ≠ a21 ∧ a02 ≠ a11 ∧ a02 ≠ a21 ∧ a11 ≠ a21) ∨ ((a00 = a11 ∧ a02 = a21) ∨ (a00 = a21 ∧ a02 = a11))) ∧
    ((a00 ≠ a01 ∧ a00 ≠ a12 ∧ a00 ≠ a22 ∧ a01 ≠ a12 ∧ a01 ≠ a22 ∧ a12 ≠ a22) ∨ ((a00 = a12 ∧ a01 = a22) ∨ (a00 = a22 ∧ a01 = a12))) ∧
    ((a11 ≠ a12 ∧ a11 ≠ a00 ∧ a11 ≠ a20 ∧ a12 ≠ a00 ∧ a12 ≠ a20 ∧ a00 ≠ a20) ∨ ((a11 = a00 ∧ a12 = a20) ∨ (a11 = a20 ∧ a12 = a00))) ∧
    ((a10 ≠ a12 ∧ a10 ≠ a01 ∧ a10 ≠ a21 ∧ a12 ≠ a01 ∧ a12 ≠ a21 ∧ a01 ≠ a21) ∨ ((a10 = a01 ∧ a12 = a21) ∨ (a10 = a21 ∧ a12 = a01))) ∧
    ((a10 ≠ a11 ∧ a10 ≠ a02 ∧ a10 ≠ a22 ∧ a11 ≠ a02 ∧ a11 ≠ a22 ∧ a02 ≠ a22) ∨ ((a10 = a02 ∧ a11 = a22) ∨ (a10 = a22 ∧ a11 = a02))) ∧
    ((a21 ≠ a22 ∧ a21 ≠ a00 ∧ a21 ≠ a10 ∧ a22 ≠ a00 ∧ a22 ≠ a10 ∧ a00 ≠ a10) ∨ ((a21 = a00 ∧ a22 = a10) ∨ (a21 = a10 ∧ a22 = a00))) ∧
    ((a20 ≠ a22 ∧ a20 ≠ a01 ∧ a20 ≠ a11 ∧ a22 ≠ a01 ∧ a22 ≠ a11 ∧ a01 ≠ a11) ∨ ((a20 = a01 ∧ a22 = a11) ∨ (a20 = a11 ∧ a22 = a01))) ∧
    ((a20 ≠ a21 ∧ a20 ≠ a02 ∧ a20 ≠ a12 ∧ a21 ≠ a02 ∧ a21 ≠ a12 ∧ a02 ≠ a12) ∨ ((a20 = a02 ∧ a21 = a12) ∨ (a20 = a12 ∧ a21 = a02))))
  (hneighbor : ((a00 ≠ a02 ∧ a00 ≠ a11 ∧ a00 ≠ a21 ∧ a02 ≠ a11 ∧ a02 ≠ a21 ∧ a11 ≠ a21) ∨ (a00 ≠ a01 ∧ a00 ≠ a12 ∧ a00 ≠ a22 ∧ a01 ≠ a12 ∧ a01 ≠ a22 ∧ a12 ≠ a22) ∨ (a11 ≠ a12 ∧ a11 ≠ a00 ∧ a11 ≠ a20 ∧ a12 ≠ a00 ∧ a12 ≠ a20 ∧ a00 ≠ a20) ∨ (a21 ≠ a22 ∧ a21 ≠ a00 ∧ a21 ≠ a10 ∧ a22 ≠ a00 ∧ a22 ≠ a10 ∧ a00 ≠ a10)) ∧
    ((a01 ≠ a02 ∧ a01 ≠ a10 ∧ a01 ≠ a20 ∧ a02 ≠ a10 ∧ a02 ≠ a20 ∧ a10 ≠ a20) ∨ (a00 ≠ a01 ∧ a00 ≠ a12 ∧ a00 ≠ a22 ∧ a01 ≠ a12 ∧ a01 ≠ a22 ∧ a12 ≠ a22) ∨ (a10 ≠ a12 ∧ a10 ≠ a01 ∧ a10 ≠ a21 ∧ a12 ≠ a01 ∧ a12 ≠ a21 ∧ a01 ≠ a21) ∨ (a20 ≠ a22 ∧ a20 ≠ a01 ∧ a20 ≠ a11 ∧ a22 ≠ a01 ∧ a22 ≠ a11 ∧ a01 ≠ a11)) ∧
    ((a01 ≠ a02 ∧ a01 ≠ a10 ∧ a01 ≠ a20 ∧ a02 ≠ a10 ∧ a02 ≠ a20 ∧ a10 ≠ a20) ∨ (a00 ≠ a02 ∧ a00 ≠ a11 ∧ a00 ≠ a21 ∧ a02 ≠ a11 ∧ a02 ≠ a21 ∧ a11 ≠ a21) ∨ (a10 ≠ a11 ∧ a10 ≠ a02 ∧ a10 ≠ a22 ∧ a11 ≠ a02 ∧ a11 ≠ a22 ∧ a02 ≠ a22) ∨ (a20 ≠ a21 ∧ a20 ≠ a02 ∧ a20 ≠ a12 ∧ a21 ≠ a02 ∧ a21 ≠ a12 ∧ a02 ≠ a12)) ∧
    ((a10 ≠ a12 ∧ a10 ≠ a01 ∧ a10 ≠ a21 ∧ a12 ≠ a01 ∧ a12 ≠ a21 ∧ a01 ≠ a21) ∨ (a10 ≠ a11 ∧ a10 ≠ a02 ∧ a10 ≠ a22 ∧ a11 ≠ a02 ∧ a11 ≠ a22 ∧ a02 ≠ a22) ∨ (a01 ≠ a02 ∧ a01 ≠ a10 ∧ a01 ≠ a20 ∧ a02 ≠ a10 ∧ a02 ≠ a20 ∧ a10 ≠ a20) ∨ (a21 ≠ a22 ∧ a21 ≠ a00 ∧ a21 ≠ a10 ∧ a22 ≠ a00 ∧ a22 ≠ a10 ∧ a00 ≠ a10)) ∧
    ((a11 ≠ a12 ∧ a11 ≠ a00 ∧ a11 ≠ a20 ∧ a12 ≠ a00 ∧ a12 ≠ a20 ∧ a00 ≠ a20) ∨ (a10 ≠ a11 ∧ a10 ≠ a02 ∧ a10 ≠ a22 ∧ a11 ≠ a02 ∧ a11 ≠ a22 ∧ a02 ≠ a22) ∨ (a00 ≠ a02 ∧ a00 ≠ a11 ∧ a00 ≠ a21 ∧ a02 ≠ a11 ∧ a02 ≠ a21 ∧ a11 ≠ a21) ∨ (a20 ≠ a22 ∧ a20 ≠ a01 ∧ a20 ≠ a11 ∧ a22 ≠ a01 ∧ a22 ≠ a11 ∧ a01 ≠ a11)) ∧
    ((a11 ≠ a12 ∧ a11 ≠ a00 ∧ a11 ≠ a20 ∧ a12 ≠ a00 ∧ a12 ≠ a20 ∧ a00 ≠ a20) ∨ (a10 ≠ a12 ∧ a10 ≠ a01 ∧ a10 ≠ a21 ∧ a12 ≠ a01 ∧ a12 ≠ a21 ∧ a01 ≠ a21) ∨ (a00 ≠ a01 ∧ a00 ≠ a12 ∧ a00 ≠ a22 ∧ a01 ≠ a12 ∧ a01 ≠ a22 ∧ a12 ≠ a22) ∨ (a20 ≠ a21 ∧ a20 ≠ a02 ∧ a20 ≠ a12 ∧ a21 ≠ a02 ∧ a21 ≠ a12 ∧ a02 ≠ a12)) ∧
    ((a20 ≠ a22 ∧ a20 ≠ a01 ∧ a20 ≠ a11 ∧ a22 ≠ a01 ∧ a22 ≠ a11 ∧ a01 ≠ a11) ∨ (a20 ≠ a21 ∧ a20 ≠ a02 ∧ a20 ≠ a12 ∧ a21 ≠ a02 ∧ a21 ≠ a12 ∧ a02 ≠ a12) ∨ (a01 ≠ a02 ∧ a01 ≠ a10 ∧ a01 ≠ a20 ∧ a02 ≠ a10 ∧ a02 ≠ a20 ∧ a10 ≠ a20) ∨ (a11 ≠ a12 ∧ a11 ≠ a00 ∧ a11 ≠ a20 ∧ a12 ≠ a00 ∧ a12 ≠ a20 ∧ a00 ≠ a20)) ∧
    ((a21 ≠ a22 ∧ a21 ≠ a00 ∧ a21 ≠ a10 ∧ a22 ≠ a00 ∧ a22 ≠ a10 ∧ a00 ≠ a10) ∨ (a20 ≠ a21 ∧ a20 ≠ a02 ∧ a20 ≠ a12 ∧ a21 ≠ a02 ∧ a21 ≠ a12 ∧ a02 ≠ a12) ∨ (a00 ≠ a02 ∧ a00 ≠ a11 ∧ a00 ≠ a21 ∧ a02 ≠ a11 ∧ a02 ≠ a21 ∧ a11 ≠ a21) ∨ (a10 ≠ a12 ∧ a10 ≠ a01 ∧ a10 ≠ a21 ∧ a12 ≠ a01 ∧ a12 ≠ a21 ∧ a01 ≠ a21)) ∧
    ((a21 ≠ a22 ∧ a21 ≠ a00 ∧ a21 ≠ a10 ∧ a22 ≠ a00 ∧ a22 ≠ a10 ∧ a00 ≠ a10) ∨ (a20 ≠ a22 ∧ a20 ≠ a01 ∧ a20 ≠ a11 ∧ a22 ≠ a01 ∧ a22 ≠ a11 ∧ a01 ≠ a11) ∨ (a00 ≠ a01 ∧ a00 ≠ a12 ∧ a00 ≠ a22 ∧ a01 ≠ a12 ∧ a01 ≠ a22 ∧ a12 ≠ a22) ∨ (a10 ≠ a11 ∧ a10 ≠ a02 ∧ a10 ≠ a22 ∧ a11 ≠ a02 ∧ a11 ≠ a22 ∧ a02 ≠ a22))) : False := by
  let p := op309_normalize_colors a00 a01 a02
  have hnorm := op309_normalize_colors_spec a00 a01 a02 hproper.1.1 hproper.1.2.1 hproper.1.2.2
  change p a00 = 0 ∧ p a01 = 1 ∧ p a02 = 2 at hnorm
  have h0 := hnorm.1
  have h1 := hnorm.2.1
  have h2 := hnorm.2.2
  apply op309_k33_normalized_normal_rich_neighbor_impossible (p a10) (p a11) (p a12) (p a20) (p a21) (p a22)
  · rw [← h0, ← h1, ← h2]
    simpa only [ne_eq, EmbeddingLike.apply_eq_iff_eq] using hproper
  · rw [← h0, ← h1, ← h2]
    simpa only [ne_eq, EmbeddingLike.apply_eq_iff_eq] using hnormal
  · rw [← h0, ← h1, ← h2]
    simpa only [ne_eq, EmbeddingLike.apply_eq_iff_eq] using hneighbor
