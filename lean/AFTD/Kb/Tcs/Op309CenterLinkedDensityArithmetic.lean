import AFTD.Prelude

/-!
# op309_center_linked_density_arithmetic

Topic: graphs   Node: 3d82bdce2ef8

Provenance: helper lemma. OP-309 center-linked P3 counting obstruction, experiment 40892.

The counting constraints force the uncovered-vertex count between 4n/13 and 5n/14.
-/

theorem op309_center_linked_density_arithmetic (n p u d : ℕ) (hn : n = 3*p + u) (hboundary : 3*u + 2*d = 5*p) (hmatch : 2*d ≤ p) : 4*n ≤ 13*u ∧ 14*u ≤ 5*n := by
  constructor <;> omega
