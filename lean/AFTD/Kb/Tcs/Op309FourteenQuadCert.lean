import AFTD.Prelude
import AFTD.Kb.Tcs.Op309FourteenIncidence

/-!
# op309_fourteen_quad_cert

Topic: graphs   Node: 3d9fd42ab2bc

Provenance: helper lemma. Finite incidence certificate for the fourteen-vertex OP-309 palette obstruction, experiments 34668, 34677, 34678.

Each of the fourteen listed base configurations is a valid three-edge nonmatching path.
-/

set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

theorem op309_fourteen_quad_cert : ∀ z : Fin 14,
    let i := op309_fourteen_quad z 0
    let j := op309_fourteen_quad z 1
    let k := op309_fourteen_quad z 2
    let l := op309_fourteen_quad z 3
    i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ l ≠ i ∧ l ≠ j ∧
    (∃ t : Fin 3, op309_fourteen_incidence i t = op309_fourteen_base j) ∧
    (∃ t : Fin 3, op309_fourteen_incidence i t = op309_fourteen_base k) ∧
    (∃ t : Fin 3, op309_fourteen_incidence l t = op309_fourteen_base j) := by
  decide
