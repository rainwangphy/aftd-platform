import AFTD.Prelude

/-!
# op874_interleaved_five_mate

Topic: graphs   Node: 3641c546936f

Provenance: helper lemma. Interleaved fixed-factor obstruction, experiments 35864 and 35866.

The mate vertex in the explicit 60-vertex factor instance.
-/

def op874_interleaved_five_mate (v : Fin 60) : Fin 60 := #[45, 46, 36, 39, 42, 31, 34, 37, 40, 43, 32, 35, 38, 41, 44, 30, 50, 55, 33, 51, 56, 47, 52, 57, 48, 53, 58, 49, 54, 59, 15, 5, 10, 18, 6, 11, 2, 7, 12, 3, 8, 13, 4, 9, 14, 0, 1, 21, 24, 27, 16, 19, 22, 25, 28, 17, 20, 23, 26, 29][v.val]!
