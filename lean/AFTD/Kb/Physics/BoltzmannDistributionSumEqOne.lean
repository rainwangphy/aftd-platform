import AFTD.Prelude
import AFTD.Kb.Physics.BoltzmannDistribution
import AFTD.Kb.Physics.CanonicalPartitionFunctionPos

/-!
# boltzmann_distribution_sum_eq_one

Topic: statistical_mechanics   Node: 5a438d28c9fc

Provenance: formalization of a published result. Source: Friedli & Velenik, Statistical Mechanics of Lattice Systems (2017), Section 1.2

For any nonempty finite configuration space Ω, Hamiltonian H : Ω → ℝ, and inverse temperature β, the sum of the Boltzmann distribution over all configurations is equal to 1.
-/

/-- The Boltzmann distribution sums to 1 over the configuration space. -/
theorem boltzmann_distribution_sum_eq_one {Ω : Type*} [Fintype Ω] [Nonempty Ω] (H : Ω → ℝ) (β : ℝ) :
    ∑ ω : Ω, boltzmannDistribution H β ω = 1 := by
  have hpos := canonical_partition_function_pos H β
  dsimp [boltzmannDistribution]
  rw [← Finset.sum_div]
  exact div_self hpos.ne'
