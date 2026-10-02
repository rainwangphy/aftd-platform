import AFTD.Prelude

/-!
# catch_up_icc_one_eq_range_toFinset

Topic: combinatorial_games   Node: b3f4a79d86d8

The set {1, ..., N} of natural numbers is the finset of the list [1, 2, ..., N].
-/

/-- `Finset.Icc 1 N` is the finset of `List.range' 1 N`. -/
theorem catch_up_icc_one_eq_range_toFinset (N : ℕ) :
    (Finset.Icc 1 N : Finset ℕ) = (List.range' 1 N).toFinset := by
  ext x
  simp only [Finset.mem_Icc, List.mem_toFinset, List.mem_range']
  constructor
  · intro h; exact ⟨x - 1, by omega, by omega⟩
  · rintro ⟨i, hi, rfl⟩; omega
