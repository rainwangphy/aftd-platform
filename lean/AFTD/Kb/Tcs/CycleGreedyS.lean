import AFTD.Prelude

/-!
# cycle_greedy_s

Topic: online_algorithms   Node: e1d460bef11a

Provenance: formalization of a published result. Source: arXiv:2610.15776, Theorem 9 (equation 13)

The rational Cayley-tree product sum `cycle_greedy_s (n : ℕ) : ℚ := ∑ d ∈ Finset.range n, ∏ j ∈ Finset.Icc 1 d, (1 - (j : ℚ) / (n : ℚ))` as a rational number for any natural number n.
-/

/-- The rational Cayley-tree product sum S_n = sum_{d=0}^{n-1} prod_{j=1}^d (1 - j / n). -/
def cycle_greedy_s (n : ℕ) : ℚ := ∑ d ∈ Finset.range n,
    ∏ j ∈ Finset.Icc 1 d, (1 - (j : ℚ) / n)
