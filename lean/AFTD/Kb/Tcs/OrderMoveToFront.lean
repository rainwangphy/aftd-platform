import AFTD.Prelude
import AFTD.Kb.Tcs.Order

/-!
# order_move_to_front

Topic: combinatorics   Node: da8e13f882dc

Provenance: formalization of a published result. Source: arXiv:2610.39311 Definition 1

The order obtained by moving attribute a to the front of order π, preserving the relative order of the remaining attributes.
-/

/-- Move attribute a to the front of order π. -/
def order_move_to_front {d : ℕ} (a : Fin d) (π : Order d) : Order d := if h : a ∈ π.elems then
    ⟨a :: π.elems.erase a,
     by rw [List.nodup_cons]; exact ⟨List.Nodup.not_mem_erase π.nodup, List.Nodup.erase a π.nodup⟩,
     by
       have hpos : 0 < π.elems.length := List.length_pos_of_mem h
       have hl := π.length_eq
       rw [List.length_cons, List.length_erase_of_mem h]
       omega⟩
  else π
