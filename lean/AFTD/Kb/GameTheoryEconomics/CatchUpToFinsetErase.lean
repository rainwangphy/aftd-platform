import AFTD.Prelude

/-!
# catch_up_toFinset_erase

Topic: combinatorial_games   Node: 3f6da9961259

For a list l of natural numbers without duplicates, erasing a from the finset of l is the finset of l with a erased.
-/

/-- Erasing commutes with `toFinset` on a duplicate-free list. -/
theorem catch_up_toFinset_erase {l : List ℕ} (hl : l.Nodup) (a : ℕ) :
    l.toFinset.erase a = (l.erase a).toFinset := by
  ext x
  simp only [Finset.mem_erase, List.mem_toFinset, hl.mem_erase_iff]
