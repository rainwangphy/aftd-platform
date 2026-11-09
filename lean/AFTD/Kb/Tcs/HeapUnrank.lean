import AFTD.Prelude
import AFTD.Kb.Tcs.HeapBlockBase
import AFTD.Kb.Tcs.PermExtendLast
import AFTD.Kb.Tcs.HeapCode

/-!
# heapUnrank

Topic: combinatorics   Node: f8ea123b08d7

Provenance: formalization of a published result. Source: arXiv:2611.05397 Definition 8

The Heap permutation unranking map heapUnrank assigns to each dimension n : ℕ and factorial-base code d : HeapCode n a permutation of Fin n. For n = 0 and n = 1, it returns the identity permutation 1. For n = k + 2, it returns the group product heapBlockBase (k + 1) q * permExtendLast (heapUnrank (k + 1) prefixCode) with the block base permutation on the left and the tail-extended recursive unrank on the right, where q = (d ⟨k, by omega⟩).val : ℕ and prefixCode : HeapCode (k + 1) is defined by prefixCode i = d ⟨i.val, by omega⟩.
-/

/-- The Heap permutation unranking map from factorial-base codes to permutations. -/
def heapUnrank : (n : ℕ) → HeapCode n → Equiv.Perm (Fin n)
  | 0, _ => 1
  | 1, _ => 1
  | k + 2, d =>
    let prefixCode : HeapCode (k + 1) := fun i => d ⟨i.val, by omega⟩
    let q : ℕ := (d ⟨k, by omega⟩).val
    heapBlockBase (k + 1) q * permExtendLast (heapUnrank (k + 1) prefixCode)
