import AFTD.Prelude

/-!
# heapBlockSwap

Topic: combinatorics   Node: ef5d3cacef8b

Provenance: formalization of a published result. Source: arXiv:2611.05397 Definition 5

The top-level transposition swap between block j and block j + 1 in the order-(n + 1) Heap algorithm, which for j < n swaps the trailing element Fin.last n with 0 if n + 1 is odd and with j if n + 1 is even, and is the identity otherwise.
-/

/-- The top-level transposition swap between adjacent blocks in the order-(n + 1) Heap algorithm. -/
def heapBlockSwap (n : ℕ) (j : ℕ) : Equiv.Perm (Fin (n + 1)) :=
  if hj : j < n then
    if (n + 1) % 2 = 1 then
      Equiv.swap ⟨0, by omega⟩ (Fin.last n)
    else
      Equiv.swap ⟨j, by omega⟩ (Fin.last n)
  else
    1
