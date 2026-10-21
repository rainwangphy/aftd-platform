import AFTD.Prelude

/-!
# is_linear_extension

Topic: algorithms   Node: db385007096f

Provenance: formalization of a published result. Source: arXiv:2610.18740 Section 5

Given a natural number n, a partial order P on Fin n, and a linear order L on Fin n, L is a linear extension of P if for all x y in Fin n, x <= y under P implies x <= y under L.
-/

/-- A linear order L on Fin n extends a partial order P if every relation in P holds in L. -/
def is_linear_extension {n : ℕ} (P : PartialOrder (Fin n)) (L : LinearOrder (Fin n)) : Prop := ∀ x y : Fin n, @LE.le (Fin n) P.toLE x y → @LE.le (Fin n) L.toLE x y
