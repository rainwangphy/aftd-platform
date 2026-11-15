import AFTD.Prelude

/-!
# poly_interval_support

Topic: combinatorics   Node: 3e09f4ada3d2

Provenance: helper lemma. step towards op_1239_max_degree_three_tree_petrial_log_concave

The coefficient support of a natural-coefficient polynomial p is an interval: whenever the coefficients at i and at k are positive and i ≤ j ≤ k, the coefficient at j is positive too (no internal zero coefficients).
-/

/-- No internal zero coefficients: the support of the coefficient sequence is an interval. -/
def poly_interval_support (p : Polynomial ℕ) : Prop := ∀ i j k : ℕ, i ≤ j → j ≤ k → 0 < p.coeff i → 0 < p.coeff k → 0 < p.coeff j
