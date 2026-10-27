import AFTD.Prelude

/-!
# six_circle_view

Topic: combinatorial_games   Node: 1f9caf9e456e

Provenance: formalization of a published result. Source: arXiv:2610.33032, Section 2 and Section 7

The local view (x, i, L, R) of the sage sitting at seat i in a circular seating π of six labeled seats consists of the sage's identity x = π i, the seat index i, the counterclockwise neighbor L = π (i - 1), and the clockwise neighbor R = π (i + 1).
-/

/-- Local view (x, i, L, R) of the sage at seat i in a circular seating π with 6 labeled seats. -/
def six_circle_view (π : Equiv.Perm (Fin 6)) (i : Fin 6) : Fin 6 × Fin 6 × Fin 6 × Fin 6 := (π i, i, π (i - 1), π (i + 1))
