import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# shellsort_h_pass

Topic: algorithms   Node: 269b2e2d3fcf

Provenance: formalization of a published result. Source: arXiv:2611.27671, Section 2 (the h-pass P_h sorts each h-chain).

The h-pass of Shellsort on an array A : Fin n → α over a linear order: for each index i, form the h-chain of i, i.e. the list of the values A j at the indices j with j % h = i % h, in increasing order of j (List.finRange n filtered, mapped by A); sort it in non-decreasing order (List.insertionSort (· ≤ ·)); the new value at i is the entry at position i / h of the sorted list, which is the position of i in its chain (List.getD with the unreachable default A i). So every chain {r, r+h, r+2h, ...} is sorted in place. For h = 0 every chain is a single index and the pass is the identity.
-/

def shellsort_h_pass {n : ℕ} {α : Type*} [LinearOrder α] (h : ℕ) (A : Fin n → α) :
    Fin n → α :=
  fun i => ((((List.finRange n).filter (fun j => j.val % h = i.val % h)).map A).insertionSort
    (· ≤ ·)).getD (i.val / h) (A i)
