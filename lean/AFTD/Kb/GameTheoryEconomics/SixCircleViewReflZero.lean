import AFTD.Prelude

/-!
# six_circle_view_refl_zero

Topic: combinatorial_games   Node: 59509a9616e3

Provenance: helper lemma. folklore

In the identity seating of six sages on a circle, the sage at seat 0 is sage 0, with seat index 0, counterclockwise neighbor 5, and clockwise neighbor 1.
-/

/-- Sanity lemma: under the identity seating, seat 0 has view (0, 0, 5, 1). -/
theorem six_circle_view_refl_zero :
    (Equiv.refl (Fin 6) 0, (0 : Fin 6), Equiv.refl (Fin 6) (0 - 1), Equiv.refl (Fin 6) (0 + 1)) =
      ((0 : Fin 6), (0 : Fin 6), (5 : Fin 6), (1 : Fin 6)) := rfl
