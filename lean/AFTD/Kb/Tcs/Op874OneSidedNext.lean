import AFTD.Prelude

/-!
# op874_one_sided_next

Topic: graphs   Node: fe5e44e59dbd

Provenance: helper lemma. Explicit fixed-factor orientation obstruction, experiments 35726–35727.

The next vertex in the explicit cycle-factor instance.
-/

def op874_one_sided_next (v : Fin 36) : Fin 36 := #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0, 12, 13, 14, 15, 16, 17, 11, 19, 20, 21, 22, 18, 24, 25, 26, 27, 23, 29, 30, 28, 32, 33, 34, 35, 31][v.val]!
