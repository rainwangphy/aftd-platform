import AFTD.Prelude

/-!
# block_snake_seq_two

Topic: fair_division   Node: 151edd4e5408

Provenance: formalization of a published result. Source: arXiv:2611.09685 Section 4.1

The block-snake picking sequence for two agents (Fin 2) dividing 2k + 1 items, represented as a List (Fin 2) of length 2k + 1 constructed via List.ofFn, where the turn index t : Fin (2 * k + 1) has picker 0 if t.val < 2 * k and t.val % 2 = 0, and picker 1 otherwise.
-/

/-- The block-snake picking sequence for two agents and 2k + 1 items. -/
def block_snake_seq_two (k : ℕ) : List (Fin 2) := List.ofFn (fun t : Fin (2 * k + 1) => if t.val % 2 = 0 ∧ t.val < 2 * k then 0 else 1)
