import AFTD.Prelude
import AFTD.Kb.Tcs.HeapCode

/-!
# heapCodeIndex

Topic: combinatorics   Node: 2d88b7cbb384

Provenance: formalization of a published result. Source: arXiv:2611.05397 Section 2.3 and Theorem 9

The generation index r(d) of a factorial-base code d, defined as the sum over i from 0 to n - 2 of d_i * (i + 1)!.
-/

/-- The generation index r(d) of a factorial-base code d in Heap's order. -/
def heapCodeIndex {n : ℕ} (d : HeapCode n) : ℕ := ∑ i : Fin (n - 1), (d i).val * (i.val + 1).factorial
