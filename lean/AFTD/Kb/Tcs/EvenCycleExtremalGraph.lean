import AFTD.Prelude

/-!
# even_cycle_extremal_graph

Topic: combinatorics   Node: 3f88a27821ff

Provenance: formalization of a published result. Source: arXiv:2611.24238 Sec. 1

The graph $H_{n,k}$ on $n$ vertices is the graph join of $K_{k-1}$ with the disjoint union of an edge $K_2$ and an independent set $I_{n-k-1}$.
-/

/-- The graph H_{n,k} = K_{k-1} ∨ (K_2 ∪ I_{n-k-1}) on n vertices. -/
def even_cycle_extremal_graph (n k : ℕ) : SimpleGraph (Fin n) where Adj u v := u ≠ v ∧ ((u.val < k - 1 ∨ v.val < k - 1) ∨
    (u.val = k - 1 ∧ v.val = k) ∨ (u.val = k ∧ v.val = k - 1))
