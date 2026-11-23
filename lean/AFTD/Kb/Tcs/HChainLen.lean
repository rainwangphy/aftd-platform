import AFTD.Prelude

/-!
# h_chain_len

Topic: algorithms   Node: e4a85d4cfb9d

Provenance: formalization of a published result. Source: arXiv:2611.27671 "Shellsort with O(n log n) Average-Case Complexity", Section 2.1

The number of valid array indices in an array of length $n$ that belong to the $h$-chain starting at residue $r$, which is $(n - 1 - r) / h + 1$ when $h > 0$ and $r < n$, and $0$ otherwise.
-/

/-- Length of the h-chain of residue r in an array of length n. -/
def h_chain_len (n h r : ℕ) : ℕ := if h = 0 ∨ n ≤ r then 0 else (n - 1 - r) / h + 1
