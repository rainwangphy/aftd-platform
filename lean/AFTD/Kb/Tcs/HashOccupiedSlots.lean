import AFTD.Prelude
import AFTD.Kb.Tcs.HashInsertStep

/-!
# hash_occupied_slots

Topic: data_structures   Node: 21f6e0e20627

Provenance: formalization of a published result. Source: arXiv:2610.31363 Section 2

The set of occupied slots in Finset (ZMod n) after sequentially inserting a list A : List (ZMod n) into an initially empty hash table of size n using offset sequence r : Fin n → ZMod n.
-/

/-- Set of occupied slots after inserting a list of elements into an initially empty hash table. -/
def hash_occupied_slots (n : ℕ) (r : Fin n → ZMod n) (A : List (ZMod n)) : Finset (ZMod n) := A.foldl (hash_insert_step n r) ∅
