import AFTD.Prelude

/-!
# op874_one_sided_prev

Topic: graphs   Node: 818c95071761

Provenance: helper lemma. Explicit fixed-factor orientation obstruction, experiments 35726–35727.

The prev vertex in the explicit cycle-factor instance.
-/

def op874_one_sided_prev (v : Fin 36) : Fin 36 := #[10, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 17, 11, 12, 13, 14, 15, 16, 22, 18, 19, 20, 21, 27, 23, 24, 25, 26, 30, 28, 29, 35, 31, 32, 33, 34][v.val]!
