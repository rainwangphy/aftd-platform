import AFTD.Prelude

/-!
# op309_center_linked_twenty_impossible

Topic: graphs   Node: 5437cb09d0a6

Provenance: helper lemma. OP-309 center-linked P3 counting obstruction, experiment 40892.

The center-linked P3 structure cannot occur on twenty vertices.
-/

theorem op309_center_linked_twenty_impossible (p u d : ℕ) (hn : 20 = 3*p + u) (hboundary : 3*u + 2*d = 5*p) (hmatch : 2*d ≤ p) : False := by omega
