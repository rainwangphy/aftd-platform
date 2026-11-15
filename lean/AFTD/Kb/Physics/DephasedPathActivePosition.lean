import AFTD.Prelude
import AFTD.Kb.Physics.DephasedPathGreedyState
import AFTD.Kb.Physics.DephasedPathGreedyChosen

/-!
# dephased_path_active_position

Topic: quantum_mechanics   Node: 6a0badd30f09

Provenance: helper lemma. step towards dephased_path_unpinned_intervals_add_greedy_matching

An unstruck active vertex: it lies in I ∩ D, the edge to its right was not chosen by the greedy matching, and its right end is either pinned off (b+1 = n and right = false) or continues inside I.
-/

open scoped Classical in
/-- An active position: a vertex of I ∩ D whose rightward edge was not chosen by the greedy scan, and which is either the last vertex with the right pin edge off, or is followed by a vertex of I. -/
def dephased_path_active_position (n : ℕ) (I D : Finset ℕ) (left right : Bool) (b : ℕ) : Prop := b ∈ I ∧ b ∈ D ∧ dephased_path_greedy_chosen n I D left right b = false ∧
    (b + 1 = n → right = false) ∧ (b + 1 ≠ n → b + 1 ∈ I)
