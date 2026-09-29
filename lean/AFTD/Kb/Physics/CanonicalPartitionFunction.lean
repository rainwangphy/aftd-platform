import AFTD.Prelude

/-!
# canonicalPartitionFunction

Topic: statistical_mechanics   Node: 61253d433246

The canonical partition function Z(β) of a system with finite configuration space Ω and Hamiltonian H : Ω → ℝ at inverse temperature β is the sum over all configurations ω of exp(-β * H(ω)).
-/

/-- The canonical partition function for a Hamiltonian on a finite configuration space at inverse temperature beta. -/
noncomputable def canonicalPartitionFunction {Ω : Type*} [Fintype Ω] (H : Ω → ℝ) (β : ℝ) : ℝ := ∑ ω : Ω, Real.exp (-β * H ω)
