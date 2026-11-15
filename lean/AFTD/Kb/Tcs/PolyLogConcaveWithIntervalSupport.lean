import AFTD.Prelude
import AFTD.Kb.Tcs.PolyIntervalSupport

/-!
# poly_log_concave_with_interval_support

Topic: combinatorics   Node: a3d985f6e503

Provenance: helper lemma. step towards op_1239_max_degree_three_tree_petrial_log_concave

A natural-coefficient polynomial p is log-concave with interval support if every triple of consecutive coefficients satisfies a_k * a_{k+2} ≤ a_{k+1}^2 and the coefficient support of p is an interval.
-/

/-- The second-half induction invariant: pointwise log-concavity of the coefficient sequence together with interval support. -/
def poly_log_concave_with_interval_support (p : Polynomial ℕ) : Prop := (∀ k : ℕ, p.coeff k * p.coeff (k + 2) ≤ p.coeff (k + 1) * p.coeff (k + 1)) ∧
    poly_interval_support p
