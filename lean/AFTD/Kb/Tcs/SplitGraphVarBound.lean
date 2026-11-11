import AFTD.Prelude

/-!
# split_graph_var_bound

Topic: graphs   Node: 526f41e69118

Provenance: formalization of a published result. Source: arXiv:2609.14826: Section 3

For natural numbers n and k, split_graph_var_bound n k is the real number defined by (k : ℝ) * ((n - k : ℕ) : ℝ) * (((n - k : ℕ) : ℝ) - 1)^2 / (n : ℝ)^2, using truncated natural subtraction n - k before casting to the real numbers.
-/

/-- Variance of the random greedy independent set size on complete split graph K_k + \bar{K}_{n-k}. -/
noncomputable def split_graph_var_bound (n k : ℕ) : ℝ := (k : ℝ) * ((n - k : ℕ) : ℝ) * (((n - k : ℕ) : ℝ) - 1) ^ 2 / ((n : ℝ) ^ 2)
