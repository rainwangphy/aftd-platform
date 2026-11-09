import AFTD.Prelude

/-!
# hardCoreSingletonVarianceLowerBound

Topic: statistical_mechanics   Node: 212ef1933ac6

Provenance: helper lemma. Singleton components in a pair of independent hard-core samples, for OP-1340.

The sum over vertices of the squared hard-core occupancy probability divided by the vertex fugacity.
-/

noncomputable def hardCoreSingletonVarianceLowerBound {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (lam : V → ℝ) : ℝ := let indep := Finset.univ.filter (fun I : Finset V => G.IsIndepSet (I : Set V)); let Z := ∑ I ∈ indep, ∏ u ∈ I, lam u; ∑ v : V, ((∑ I ∈ indep.filter (fun I => v ∈ I), ∏ u ∈ I, lam u) / Z) ^ 2 / lam v
