import AFTD.Prelude
import AFTD.Kb.Tcs.GroupHashInsertStep

/-!
# group_hash_occupied_slots

Topic: data_structures   Node: f26be2489637

Provenance: formalization of a published result. Source: arXiv:2610.31363; OP-808

The set of occupied slots in Finset G after sequentially inserting a list of keys A : List G into an initially empty hash table on group G of size n using offset sequence r : Fin n → G.
-/

/-- Set of occupied slots after sequentially inserting a list of keys A into an initially empty group hash table. -/
def group_hash_occupied_slots {G : Type*} [Group G] [DecidableEq G]
    (n : ℕ) (r : Fin n → G) (A : List G) : Finset G := A.foldl (group_hash_insert_step n r) ∅
