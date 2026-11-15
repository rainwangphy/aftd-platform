import AFTD.Prelude

/-!
# slow_exact_nim_geometric_padded_witness

Topic: combinatorial_games   Node: 3b4808d0da8a

Provenance: original. Related work: arXiv:2611.14546; OP-1728

For natural numbers r and k, slow_exact_nim_geometric_padded_witness r k is the position on k + r piles (represented as a function from Fin (k + r) to ℕ) defined by mapping each index i with i.val ≤ r to 2^(i.val) and every index i with i.val > r to 2^(r+1) - 1.
-/

/-- The geometric padded witness position on k+r piles: powers of two 2^i for i ≤ r, and 2^(r+1)-1 for the remaining k-1 piles. -/
def slow_exact_nim_geometric_padded_witness (r k : ℕ) : Fin (k + r) → ℕ := fun i => if i.val ≤ r then 2 ^ i.val else 2 ^ (r + 1) - 1
