import AFTD.Prelude
import AFTD.Kb.Physics.DephasedPathActiveEdge

/-!
# dephased_path_greedy_state

Topic: quantum_mechanics   Node: 4a608be1ac3e

Provenance: helper lemma. step towards dephased_path_unpinned_intervals_add_greedy_matching

Folding the greedy step over the edge positions 0,…,m-1 yields the flag "the edge at m-1 was chosen" together with the number of edges chosen so far.
-/

open scoped Classical in
/-- State of the left-to-right greedy matching after processing the edge positions 0, …, m-1: a "was the last processed edge chosen" flag together with the number of chosen edges. -/
def dephased_path_greedy_state (n : ℕ) (I D : Finset ℕ) (left right : Bool) (m : ℕ) : Bool × ℕ := (List.range m).foldl
    (fun acc e =>
      if dephased_path_active_edge n I D left right e && !acc.1 then (true, acc.2 + 1)
      else (false, acc.2)) (false, 0)
