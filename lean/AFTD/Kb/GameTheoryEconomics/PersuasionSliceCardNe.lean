import AFTD.Prelude

/-!
# persuasion_slice_card_ne

Topic: mechanism_design   Node: 33af998c9ff6

Each point of Fin (2m+1) differs from exactly 2m points.
-/

open Finset in
/-- Each point of `Fin (2m+1)` differs from exactly `2m` points. -/
lemma persuasion_slice_card_ne (m : ℕ) (s : Fin (2 * m + 1)) :
    (Finset.univ.filter (fun t : Fin (2 * m + 1) => s ≠ t)).card = 2 * m := by
  rw [filter_ne, card_erase_of_mem (Finset.mem_univ s), card_univ, Fintype.card_fin]
  omega
