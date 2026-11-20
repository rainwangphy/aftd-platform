import AFTD.Prelude

/-!
# op874_two_sided_five_next

Topic: graphs   Node: e36423700e7a

Provenance: helper lemma. Two-sided fixed-factor five-cycle obstruction, experiment 35839.

The next vertex in the explicit 60-vertex factor instance.
-/

def op874_two_sided_five_next (v : Fin 60) : Fin 60 := #[1, 2, 3, 4, 0, 6, 7, 8, 9, 5, 11, 12, 13, 14, 10, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 15, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 30, 46, 47, 48, 49, 45, 51, 52, 53, 54, 50, 56, 57, 58, 59, 55][v.val]!
