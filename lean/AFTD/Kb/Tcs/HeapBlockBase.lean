import AFTD.Prelude
import AFTD.Kb.Tcs.HeapBlockSwap
import AFTD.Kb.Tcs.PermExtendLast
import AFTD.Kb.Tcs.HeapFinalPerm

/-!
# heapBlockBase

Topic: combinatorics   Node: e17f9ce79c44

Provenance: formalization of a published result. Source: arXiv:2611.05397 Definition 7

The block base permutation for the q-th block of the order-(n + 1) Heap algorithm, defined recursively with the 0-th block base as the identity, and the (q + 1)-th obtained from the q-th by composing with the tail-extended final permutation of order n and the block transition swap.
-/

/-- The block base permutation C_{n+1, q} of the order-(n + 1) Heap algorithm. -/
def heapBlockBase (n : ℕ) : ℕ → Equiv.Perm (Fin (n + 1))
  | 0 => 1
  | q + 1 => heapBlockBase n q * permExtendLast (heap_final_perm n) * heapBlockSwap n q
