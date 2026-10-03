import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PersuasionSliceCoord

/-!
# persuasion_slice_card_filter

Topic: mechanism_design   Node: 7cca0dc8389f

Counting coordinates of the slice prior with a property of the underlying m-subset is counting m-subsets of Fin (2m+1) with that property.
-/

open Finset in
/-- Counting coordinates of the slice prior with a property of the underlying `m`-subset is counting `m`-subsets of `Fin (2m+1)` with that property. -/
lemma persuasion_slice_card_filter (m : ℕ) (P : Finset (Fin (2 * m + 1)) → Prop)
    [DecidablePred P] :
    (Finset.univ.filter (fun i : persuasion_slice_coord m => P i.1)).card =
      ((powersetCard m Finset.univ).filter P).card := by
  rw [← card_map (Function.Embedding.subtype _)]
  congr 1
  ext x
  simp only [mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Function.Embedding.coe_subtype,
    mem_powersetCard, Finset.subset_univ]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨i.2, hi⟩
  · rintro ⟨hx, hP⟩; exact ⟨⟨x, hx⟩, hP, rfl⟩
