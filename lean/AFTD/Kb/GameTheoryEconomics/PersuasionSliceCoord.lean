import AFTD.Prelude

/-!
# persuasion_slice_coord

Topic: mechanism_design   Node: 171ac68de938

Coordinates of the slice prior: the m-subsets of Fin (2m+1).
-/

open Finset in
/-- Coordinates of the slice prior: the `m`-subsets of `Fin (2m+1)`. -/
abbrev persuasion_slice_coord (m : ℕ) := {i : Finset (Fin (2 * m + 1)) // i.card = m}
