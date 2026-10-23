import AFTD.Prelude
import AFTD.Kb.Tcs.HashOccupiedSlots

/-!
# hash_occupied_slots_nil

Topic: data_structures   Node: e71cc4be44ad

Provenance: helper lemma. arXiv:2610.31363 Section 2

For any n and offset sequence r : Fin n → ZMod n, hash_occupied_slots n r [] = ∅.
-/

/-- Inserting an empty sequence results in no occupied slots. -/
theorem hash_occupied_slots_nil (n : ℕ) (r : Fin n → ZMod n) :
    hash_occupied_slots n r [] = ∅ := rfl
