import AFTD.Prelude
import AFTD.Kb.Tcs.IsUniqueExtremalForEvenCycles

/-!
# even_cycle_order_threshold

Topic: combinatorics   Node: ccd0dad11dcc

Provenance: formalization of a published result. Source: arXiv:2611.24238 Sec. 5, Question 1

The order threshold $n_0(k, \\ell)$ is the smallest integer such that for every integer $n \\ge n_0(k, \\ell)$, $H_{n,k}$ is the unique $n$-vertex $C_{2k}$-free graph maximizing the number of unlabeled copies of $C_{2\\ell}$.
-/

/-- The order threshold n_0(k, l), the smallest integer such that H_{n,k} is the unique extremal graph for all n ≥ n_0. -/
noncomputable def even_cycle_order_threshold (k l : ℕ) : ℕ := sInf { n₀ : ℕ | ∀ n ≥ n₀, is_unique_extremal_for_even_cycles n k l }
