import AFTD.Prelude

/-!
# guaranteed_rollercoaster_length

Topic: algorithms   Node: 29483e8d14cf

Provenance: formalization of a published result. Source: arXiv:2611.26297, Thm. 1

The maximum guaranteed length f_k(n) of a k-rollercoaster subsequence in any permutation of length n: 0 for n ≤ (k-1)², 2(k-1) - ⌊√(2(k-1)² - n)⌋ for (k-1)² < n < 2(k-1)², and ⌈n/(k-1)⌉ for n ≥ 2(k-1)².
-/

/-- The maximum guaranteed length f_k(n) of a k-rollercoaster in an n-element permutation. -/
def guaranteed_rollercoaster_length (k n : ℕ) : ℕ :=
  let q := k - 1
  if n ≤ q ^ 2 then 0
  else if n < 2 * q ^ 2 then 2 * q - Nat.sqrt (2 * q ^ 2 - n)
  else (n + q - 1) / q
