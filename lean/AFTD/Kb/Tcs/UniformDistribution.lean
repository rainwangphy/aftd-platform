import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# uniformDistribution

Topic: information   Node: ad6e0691a70c

Provenance: formalization of a published result. Source: arXiv:2610.01563 Lemma 3

The uniform distribution $U_k$ on $\{1, \dots, k\}$, viewed as a function on $\mathbb{N}^+$, evaluates to $1/k$ for $n \le k$ and $0$ for $n > k$.
-/

/-- Uniform probability distribution on {1, ..., k} viewed as a function on ℕ+. -/
noncomputable def uniformDistribution (k : ℕ+) (n : ℕ+) : ℝ := if n ≤ k then 1 / (k : ℝ) else 0
