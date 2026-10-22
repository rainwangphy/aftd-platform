import AFTD.Prelude

/-!
# cyclic_shift

Topic: information   Node: cb174a032742

Provenance: formalization of a published result. Source: arXiv:2610.28047 Section 2.3

The right cyclic shift operator on a vector v : Fin n → F over a type F, mapping each index i to v ((i + n - 1) % n) when n ≠ 0, and returning v when n = 0.
-/

/-- The right cyclic shift operator on vectors of length n. -/
def cyclic_shift (n : ℕ) {F : Type*} (v : Fin n → F) : Fin n → F := if hn : n = 0 then v
  else fun i => v ⟨(i.val + n - 1) % n, Nat.mod_lt _ (Nat.pos_of_ne_zero hn)⟩
