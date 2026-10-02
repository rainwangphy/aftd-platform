import AFTD.Prelude

/-!
# cyclic_offset

Topic: matching_markets   Node: 3993b7b32a65

For i, j in {0, ..., n-1}, the forward cyclic offset from i to j is (j - i) mod n, a number in {0, ..., n-1}.
-/

/-- The forward offset from `i` to `j` on `ℤ/nℤ`: `(j - i) mod n`, as a natural number below `n`. -/
def cyclic_offset {n : ℕ} (i j : Fin n) : ℕ := (j.val + n - i.val) % n
