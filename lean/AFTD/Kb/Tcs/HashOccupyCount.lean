import AFTD.Prelude
import AFTD.Kb.Tcs.HashOccupiedSlots

/-!
# hash_occupy_count

Topic: data_structures   Node: e1b210aeda27

Provenance: formalization of a published result. Source: arXiv:2610.31363 Definition 3.1

The number of slots in S : Finset (ZMod n) that are occupied after inserting the list A : List (ZMod n) into an initially empty table of size n using offset sequence r : Fin n → ZMod n, defined as (hash_occupied_slots n r A ∩ S).card.
-/

/-- The number of slots in S occupied after inserting sequence A. -/
def hash_occupy_count (n : ℕ) (r : Fin n → ZMod n) (S : Finset (ZMod n)) (A : List (ZMod n)) : ℕ := (hash_occupied_slots n r A ∩ S).card
