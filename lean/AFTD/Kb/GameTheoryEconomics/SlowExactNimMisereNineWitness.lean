import AFTD.Prelude

/-!
# slow_exact_nim_misere_nine_witness

Topic: combinatorial_games   Node: 0110f7682ff3

Provenance: formalization of a published result. Source: arXiv:2611.14546, Section 1 and OP-2051

For a natural number k, slow_exact_nim_misere_nine_witness k is the position on k + 2 piles assigning 4 to index 0, 9 to index 1, 14 to index 2, 15 to index 3, and 20 to all remaining indices.
-/

/-- Witness position family on k+2 piles with entries 4, 9, 14, 15 followed by k-2 copies of 20. -/
def slow_exact_nim_misere_nine_witness (k : ℕ) : Fin (k + 2) → ℕ := fun i =>
  if i.val = 0 then 4
  else if i.val = 1 then 9
  else if i.val = 2 then 14
  else if i.val = 3 then 15
  else 20
