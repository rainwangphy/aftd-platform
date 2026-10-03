import AFTD.Prelude

/-!
# cyclic_two_orientation

Topic: fair_division   Node: 6ba0268ec207

The orientation of the complete graph on n vertices with arcs i -> i+1 and i -> i+2 (mod n).
-/

/-- The orientation `i → i + 1, i → i + 2 (mod n)` of the complete graph on `Fin n`. -/
def cyclic_two_orientation (n : ℕ) (i j : Fin n) : Bool :=
  decide ((j.val + n - i.val) % n = 1 ∨ (j.val + n - i.val) % n = 2)
