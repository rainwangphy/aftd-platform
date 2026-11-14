import AFTD.Prelude
import AFTD.Kb.Physics.HypergraphDeficitH

/-!
# hypergraph_binomial_deficit

Topic: quantum_mechanics   Node: 8ab124834c94

Provenance: formalization of a published result. Source: arXiv:2610.42129; OP-1668

For any natural number n and real number p, the binomial deficit hypergraph_binomial_deficit n p is the expectation with respect to W ~ Binomial(n, p) of (3/16)*(n - 2W)^2 * hypergraph_deficit_h p |n - 2W| + (9/16)*((n - W)*hypergraph_deficit_h p |n - 2W - 1| + W*hypergraph_deficit_h p |n - 2W + 1|).
-/

/-- The quantum Fisher information binomial deficit D_n(p) for the complete weighted hypergraph state. -/
noncomputable def hypergraph_binomial_deficit (n : ℕ) (p : ℝ) : ℝ := ∑ w ∈ Finset.range (n + 1),
    (n.choose w : ℝ) * p ^ w * (1 - p) ^ (n - w) *
      ((3 / 16 : ℝ) * ((n : ℝ) - 2 * (w : ℝ)) ^ 2 * hypergraph_deficit_h p ((n : ℤ) - 2 * (w : ℤ)).natAbs +
       (9 / 16 : ℝ) * (((n : ℝ) - (w : ℝ)) * hypergraph_deficit_h p ((n : ℤ) - 2 * (w : ℤ) - 1).natAbs +
                       (w : ℝ) * hypergraph_deficit_h p ((n : ℤ) - 2 * (w : ℤ) + 1).natAbs))
