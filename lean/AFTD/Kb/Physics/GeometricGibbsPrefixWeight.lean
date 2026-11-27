import AFTD.Prelude
import AFTD.Kb.Physics.GeometricGibbs

/-!
# geometric_gibbs_prefix_weight

Topic: quantum_mechanics   Node: 867d1aa786c7

Provenance: formalization of a published result. Source: arXiv:2610.35433

For natural numbers N and j and real number q, the prefix weight geometric_gibbs_prefix_weight N q j is the sum of geometric_gibbs N q i over all indices i : Fin N with (i : ℕ) < j.
-/

/-- Cumulative Gibbs weight of the first j levels as a sum. -/
noncomputable def geometric_gibbs_prefix_weight (N : ℕ) (q : ℝ) (j : ℕ) : ℝ := ∑ i ∈ Finset.filter (fun (i : Fin N) => (i : ℕ) < j) Finset.univ, geometric_gibbs N q i
