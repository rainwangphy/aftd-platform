import AFTD.Prelude

/-!
# cyclic_rotate_left

Topic: information   Node: 7acbacec192d

Provenance: formalization of a published result. Source: folklore

Given a type α, a natural number k, and a word w : Fin k → α, cyclic_rotate_left k w is the function Fin k → α mapping each index j : Fin k to w evaluated at the index (j.val + 1) % k.
-/

/-- The 1-step cyclic left-shift of a length-k word w. -/
def cyclic_rotate_left {α : Type*} (k : ℕ) (w : Fin k → α) : Fin k → α := fun j => w ⟨(j.val + 1) % k, Nat.mod_lt _ (pos_of_gt j.isLt)⟩
