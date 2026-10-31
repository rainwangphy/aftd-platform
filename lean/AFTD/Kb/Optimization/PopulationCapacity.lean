import AFTD.Prelude
import AFTD.Kb.Optimization.BlockPopulationCapacity

/-!
# population_capacity

Topic: submodular   Node: 2c5837826d57

Provenance: formalization of a published result. Source: arXiv:2610.35433 Eq. 5

Given a Gibbs vector γ, an initial state x on Fin n, and a subset S of energy levels, the population capacity is the supremum over all thermally reachable populations of the total population in S.
-/

/-- Population capacity of a subset S of energy levels for an initial state x and Gibbs vector γ. -/
noncomputable def population_capacity {n : ℕ} (γ x : Fin n → ℝ) : Finset (Fin n) → ℝ := block_population_capacity id γ x
