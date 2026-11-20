import AFTD.Prelude

/-!
# op874_seven_cycle_separated_capacity

Topic: combinatorics   Node: 5a520e672e19

Provenance: helper lemma. Separated ownership capacity obstruction, experiment 35686.

A seven-cycle contains at most two selected vertices when selected vertices are separated by at least three cyclic positions.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0

theorem op874_seven_cycle_separated_capacity (S : Finset (Fin 7))
    (hs : ∀ x ∈ S, x+1 ∉ S ∧ x+2 ∉ S) : S.card ≤ 2 := by
  revert S
  decide
