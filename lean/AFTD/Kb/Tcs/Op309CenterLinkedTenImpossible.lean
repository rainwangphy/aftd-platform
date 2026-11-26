import AFTD.Prelude

/-!
# op309_center_linked_ten_impossible

Topic: graphs   Node: 57a5680a60b4

Provenance: helper lemma. OP-309 center-linked P3 counting obstruction, experiment 40892.

The center-linked P3 structure cannot occur on ten vertices.
-/

theorem op309_center_linked_ten_impossible (p u d : ℕ) (hn : 10 = 3*p + u) (hboundary : 3*u + 2*d = 5*p) (hmatch : 2*d ≤ p) : False := by omega
