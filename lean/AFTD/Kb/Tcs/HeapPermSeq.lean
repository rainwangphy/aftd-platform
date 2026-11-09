import AFTD.Prelude
import AFTD.Kb.Tcs.HeapBlockBase
import AFTD.Kb.Tcs.PermExtendLast

/-!
# heapPermSeq

Topic: combinatorics   Node: 865fb1d1279d

Provenance: formalization of a published result. Source: arXiv:2611.05397 Lemma 2

The r-th permutation in the Heap output sequence of order n, defined for order k + 2 by decomposing r into block index q = r / (k + 1)! and in-block index rem = r % (k + 1)!, composing the block base array with the tail-extended rem-th permutation of order k + 1.
-/

/-- The r-th permutation in the Heap output sequence of order n. -/
def heapPermSeq : (n : ℕ) → ℕ → Equiv.Perm (Fin n)
  | 0, _ => 1
  | 1, _ => 1
  | k + 2, r =>
    let f := (k + 1).factorial
    let q := r / f
    let rem := r % f
    heapBlockBase (k + 1) q * permExtendLast (heapPermSeq (k + 1) rem)
