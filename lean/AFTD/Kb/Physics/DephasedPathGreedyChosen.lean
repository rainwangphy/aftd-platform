import AFTD.Prelude
import AFTD.Kb.Physics.DephasedPathGreedyState

/-!
# dephased_path_greedy_chosen

Topic: quantum_mechanics   Node: 2fb3ffaac905

Provenance: helper lemma. step towards dephased_path_unpinned_intervals_add_greedy_matching

The greedy matching has just chosen the edge ending at b+1 exactly when the fold over the positions 0,…,b ends in the "chosen" state.
-/

open scoped Classical in
/-- Whether the left-to-right greedy matching chose the edge ending at position b+1, i.e. the flag after processing positions 0, …, b. -/
def dephased_path_greedy_chosen (n : ℕ) (I D : Finset ℕ) (left right : Bool) (b : ℕ) : Bool := (dephased_path_greedy_state n I D left right (b + 1)).1
