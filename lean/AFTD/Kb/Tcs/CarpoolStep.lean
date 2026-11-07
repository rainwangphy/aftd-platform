import AFTD.Prelude

/-!
# carpool_step

Topic: online_algorithms   Node: f89cf3af3460

Provenance: formalization of a published result. Source: arXiv:2611.00388 Eq (1.1), Online carpooling against an oblivious adversary

In online carpooling on n vertices, given an edge e joining two distinct vertices and an orientation bit b, the discrepancy vector d updates by adding 1 to e.1 and -1 to e.2 if b is true, and the opposite if b is false.
-/

/-- One step of discrepancy update in online carpooling for an edge e with orientation sign b. -/
def carpool_step (n : ℕ) (d : Fin n → ℤ) (e : Fin n × Fin n) (b : Bool) : Fin n → ℤ := fun v => d v +
    (if v = e.1 then (if b then 1 else -1) else 0) +
    (if v = e.2 then (if b then -1 else 1) else 0)
