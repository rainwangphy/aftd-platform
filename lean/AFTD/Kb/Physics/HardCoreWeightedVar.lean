import AFTD.Prelude

/-!
# hardCoreWeightedVar

Topic: statistical_mechanics   Node: 6a3a54066320

Provenance: original. Related work: OP-1355

Given a finite graph G on a type V with decidable equality, vertex fugacities lam, and observable weights a, hardCoreWeightedVar G lam a is the variance of the observable ∑_{v ∈ I} a v for an independent set I chosen with probability proportional to ∏_{v ∈ I} lam v.
-/

/-- Variance of a weighted independent set observable under the hard-core measure. -/
noncomputable def hardCoreWeightedVar {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (lam : V → ℝ) (a : V → ℝ) : ℝ :=
  have indep : Finset (Finset V) := {I | G.IsIndepSet (↑I : Set V)};
  have Z := ∑ I ∈ indep, ∏ v ∈ I, lam v;
  have E1 := (∑ I ∈ indep, (∏ v ∈ I, lam v) * (∑ v ∈ I, a v)) / Z;
  have E2 := (∑ I ∈ indep, (∏ v ∈ I, lam v) * (∑ v ∈ I, a v) ^ 2) / Z;
  E2 - E1 ^ 2
