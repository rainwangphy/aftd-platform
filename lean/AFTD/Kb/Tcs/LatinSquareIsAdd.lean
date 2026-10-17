import AFTD.Prelude
import AFTD.Kb.Tcs.LatinSquareIs

/-!
# latin_square_is_add

Topic: combinatorics   Node: fbc10041f3d5

Provenance: helper lemma. Sanity lemma for Latin squares, arXiv:2610.20008 (Avoiding a partial Latin square with an isotope of a given Latin square).

Sanity check: the addition table of Z/n is a Latin square.
-/

theorem latin_square_is_add (n : ℕ) [NeZero n] : latin_square_is fun i j : Fin n => i + j :=
  ⟨fun i _ _ h => add_left_cancel h, fun j _ _ h => add_right_cancel h⟩
