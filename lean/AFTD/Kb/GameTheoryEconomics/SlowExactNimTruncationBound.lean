import AFTD.Prelude

/-!
# slow_exact_nim_truncation_bound

Topic: combinatorial_games   Node: 30697500b3f1

Provenance: formalization of a published result. Source: arXiv:2611.14546:182

The truncation bound L for a position x on k+1 piles in slow exact k-Nim, defined as the infimum of ⌊(∑_{i < j} x_i) / (j-1)⌋ over all j in the interval [2, k+1].
-/

/-- The truncation bound L for a position x on k+1 piles in slow exact k-Nim, defined as the minimum over 2 ≤ j ≤ k+1 of ⌊P_j / (j-1)⌋. -/
noncomputable def slow_exact_nim_truncation_bound (k : ℕ) (x : Fin (k + 1) → ℕ) : ℕ := sInf ((fun j => (∑ i : Fin (k + 1), if i.val < j then x i else 0) / (j - 1)) '' (Set.Icc 2 (k + 1)))
