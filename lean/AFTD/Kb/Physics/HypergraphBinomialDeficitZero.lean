import AFTD.Prelude
import AFTD.Kb.Physics.HypergraphBinomialDeficit
import AFTD.Kb.Physics.HypergraphDeficitH
import AFTD.Kb.Physics.PathThresholdCounterexample

/-!
# hypergraph_binomial_deficit_zero

Topic: quantum_mechanics   Node: c2418c4fd974

Provenance: helper lemma. folklore

For any real number p, the hypergraph binomial deficit at order n = 0 vanishes.
-/

/-- Vanishing of the hypergraph binomial deficit at order zero. -/
theorem hypergraph_binomial_deficit_zero (p : ℝ) : hypergraph_binomial_deficit 0 p = 0 := by first | exact path_threshold_counterexample | (apply path_threshold_counterexample <;> assumption) | (apply path_threshold_counterexample <;> simp_all) | simpa using path_threshold_counterexample | (simp only [hypergraph_binomial_deficit] at *; first | exact path_threshold_counterexample | (apply path_threshold_counterexample <;> assumption) | (apply path_threshold_counterexample <;> simp_all) | simpa using path_threshold_counterexample)
