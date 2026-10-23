import AFTD.Prelude
import AFTD.Kb.Tcs.HashOccupyCount
import AFTD.Kb.Tcs.HashOccupiedSlotsNil
import AFTD.Kb.Tcs.HashOccupiedSlots

/-!
# hash_occupy_count_nil

Topic: data_structures   Node: 0fba5f45823c

Provenance: helper lemma. arXiv:2610.31363 Definition 3.1

For any n, r : Fin n → ZMod n, and S : Finset (ZMod n), hash_occupy_count n r S [] = 0.
-/

/-- Occupy count of an empty sequence is zero. -/
theorem hash_occupy_count_nil (n : ℕ) (r : Fin n → ZMod n) (S : Finset (ZMod n)) :
    hash_occupy_count n r S [] = 0 := by
  simp [hash_occupy_count, hash_occupied_slots_nil]
