import AFTD.Prelude

/-!
# slow_exact_nim_unit_shift

Topic: combinatorial_games   Node: 6167d4596a56

Provenance: formalization of a published result. Source: arXiv:2611.14546, Section 7.1

For any natural number k and position x on k+1 piles, slow_exact_nim_unit_shift k x is the position that leaves pile 0 unchanged and increases every pile i with i.val ≠ 0 by 1.
-/

/-- The unit-shift operator T adding one stone to every pile except the first in slow exact k-Nim with k+1 piles. -/
def slow_exact_nim_unit_shift (k : ℕ) (x : Fin (k + 1) → ℕ) : Fin (k + 1) → ℕ := fun i => if i.val = 0 then x i else x i + 1
