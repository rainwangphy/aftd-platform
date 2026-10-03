import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PersuasionSliceCoord

/-!
# persuasion_slice_card_coord

Topic: mechanism_design   Node: 4cac375fad40

The slice prior has C(2m+1, m) coordinates.
-/

open Finset in
/-- The slice prior has `C(2m+1, m)` coordinates. -/
lemma persuasion_slice_card_coord (m : ℕ) :
    Fintype.card (persuasion_slice_coord m) = (2 * m + 1).choose m := by
  rw [Fintype.card_subtype]
  have : (Finset.univ.filter fun i : Finset (Fin (2 * m + 1)) => i.card = m) = powersetCard m Finset.univ := by
    ext i; simp [mem_powersetCard]
  rw [this, card_powersetCard, card_univ, Fintype.card_fin]
