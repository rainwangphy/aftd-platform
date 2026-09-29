import AFTD.Prelude
import AFTD.Kb.Physics.CanonicalPartitionFunction

/-!
# boltzmannDistribution

Topic: statistical_mechanics   Node: cb942a6ac371

The Boltzmann (Gibbs) distribution on a finite configuration space Ω with Hamiltonian H : Ω → ℝ at inverse temperature β assigns to each configuration ω the probability exp(-β * H(ω)) / Z(β), where Z(β) is the canonical partition function.
-/

/-- The Boltzmann (Gibbs) distribution associated with a Hamiltonian H at inverse temperature beta. -/
noncomputable def boltzmannDistribution {Ω : Type*} [Fintype Ω] (H : Ω → ℝ) (β : ℝ) (ω : Ω) : ℝ := Real.exp (-β * H ω) / canonicalPartitionFunction H β
