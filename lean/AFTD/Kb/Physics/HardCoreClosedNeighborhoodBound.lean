import AFTD.Prelude

/-!
# hardCoreClosedNeighborhoodBound

Topic: statistical_mechanics   Node: b515bf1ec612

Provenance: original. Related work: OP-1340; knowledgebase

Given a finite graph G on a type V with decidable equality and positive vertex fugacities lam, the closed-neighborhood variance lower bound hardCoreClosedNeighborhoodBound G lam is defined as the sum over all vertices v of lam v / (1 + ∑_{u ∈ N[v]} lam u)^2, where N[v] is the closed neighborhood insert v (G.neighborFinset v).
-/

/-- The closed neighborhood lower bound for the hard-core variance, defined as ∑_v λ_v / (1 + ∑_{u ∈ N[v]} λ_u)^2. -/
noncomputable def hardCoreClosedNeighborhoodBound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (lam : V → ℝ) : ℝ := ∑ v : V, lam v / (1 + ∑ u ∈ insert v (G.neighborFinset v), lam u) ^ 2
