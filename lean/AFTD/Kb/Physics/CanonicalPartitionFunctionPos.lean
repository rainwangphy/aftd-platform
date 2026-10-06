import AFTD.Prelude
import AFTD.Kb.Physics.CanonicalPartitionFunction

/-!
# canonical_partition_function_pos

Topic: statistical_mechanics   Node: 4b2c23f6f066

Provenance: helper lemma. Friedli & Velenik, Statistical Mechanics of Lattice Systems (2017), Section 1.2

For any nonempty finite configuration space Ω, Hamiltonian H : Ω → ℝ, and inverse temperature β, the canonical partition function is strictly positive.
-/

/-- The canonical partition function of a nonempty finite system is strictly positive. -/
theorem canonical_partition_function_pos {Ω : Type*} [Fintype Ω] [Nonempty Ω] (H : Ω → ℝ) (β : ℝ) :
    0 < canonicalPartitionFunction H β := by
  unfold canonicalPartitionFunction
  obtain ⟨ω₀⟩ := (inferInstance : Nonempty Ω)
  exact Finset.sum_pos' (fun ω _ => (Real.exp_pos _).le) ⟨ω₀, Finset.mem_univ ω₀, Real.exp_pos _⟩
