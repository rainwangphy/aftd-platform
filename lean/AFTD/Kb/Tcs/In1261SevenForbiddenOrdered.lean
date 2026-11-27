import AFTD.Prelude

/-!
# in1261_seven_forbidden_ordered

Topic: graphs   Node: 086bd2bac209

Provenance: helper lemma. OP-1957: seven-by-seven boundary control, experiment 43349, arXiv:2611.22690.

Ordered forbidden pairs of the explicit seven-by-seven boundary control graph.
-/

def in1261_seven_forbidden_ordered (i j : ℕ) : Prop :=
  (i < 7 ∧ 7 ≤ j ∧ j < 14) ∨
  (14 ≤ i ∧ i < 21 ∧ 21 ≤ j) ∨
  (i = 0 ∧ ((1 ≤ j ∧ j ≤ 3) ∨ j = 21)) ∨
  (1 ≤ i ∧ i ≤ 3 ∧ (j = 14 ∨ j = 21)) ∨
  (7 ≤ i ∧ i < j ∧ j < 14 ∧ j-i ≠ 1 ∧ (i,j) ≠ (7,13)) ∨
  (15 ≤ i ∧ i < j ∧ j ≤ 20 ∧ (i,j) ≠ (15,16) ∧ (i,j) ≠ (17,18) ∧ (i,j) ≠ (19,20))
