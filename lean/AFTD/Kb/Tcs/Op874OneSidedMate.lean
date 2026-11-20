import AFTD.Prelude

/-!
# op874_one_sided_mate

Topic: graphs   Node: 6641984082ab

Provenance: helper lemma. Explicit fixed-factor orientation obstruction, experiments 35726–35727.

The mate vertex in the explicit cycle-factor instance.
-/

def op874_one_sided_mate (v : Fin 36) : Fin 36 := #[32, 28, 29, 25, 30, 21, 27, 34, 19, 23, 35, 26, 33, 22, 20, 24, 31, 18, 17, 8, 14, 5, 13, 9, 15, 3, 11, 6, 1, 2, 4, 16, 0, 12, 7, 10][v.val]!
