import AFTD.Prelude

/-!
# hardCoreWeightedClosedNeighborhoodBound

Topic: statistical_mechanics   Node: 29ef7e031e7b

Provenance: original. Related work: OP-1355

Given a finite graph G on a type V with decidable equality, vertex fugacities lam, and observable weights a, hardCoreWeightedClosedNeighborhoodBound G lam a is the sum over all vertices v of (a v)^2 * lam v / (1 + ∑_{u ∈ N[v]} lam u)^2, where N[v] is the closed neighborhood of v.
-/

/-- The closed-neighborhood lower bound for the weighted hard-core variance. -/
noncomputable def hardCoreWeightedClosedNeighborhoodBound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (lam : V → ℝ) (a : V → ℝ) : ℝ :=
  ∑ v, (a v ^ 2 * lam v) / (1 + ∑ u ∈ insert v (G.neighborFinset v), lam u) ^ 2
