import AFTD.Prelude

/-!
# finset_sdiff_card_le_erase_sdiff_card_add_one

Topic: graphs   Node: 11700976b334

Provenance: helper lemma. OP-1957: graph-to-count transfer for the size-five block forced-edge route (IN-1126).

Erasing one element from a finite set lowers the size of its difference with any set by at most one.
-/

theorem finset_sdiff_card_le_erase_sdiff_card_add_one {V : Type*} [DecidableEq V] (s Q : Finset V) (y : V) :
    (s \ Q).card ≤ ((s.erase y) \ Q).card + 1 := by
  have hsub : s \ Q ⊆ insert y ((s.erase y) \ Q) := by
    intro w hw
    rw [Finset.mem_sdiff] at hw
    by_cases h : w = y
    · simp [h]
    · simp [Finset.mem_sdiff, Finset.mem_erase, h, hw.1, hw.2]
  exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
