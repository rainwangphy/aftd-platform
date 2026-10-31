import AFTD.Prelude
import AFTD.Kb.Optimization.ThermallyReachableBlockPopulations

/-!
# block_population_capacity

Topic: submodular   Node: d8eac3d14334

Provenance: formalization of a published result. Source: arXiv:2610.35433:146

Given a block-assignment map proj : Fin n → Fin m, vectors γ, x : Fin n → ℝ, and a subset S : Finset (Fin m), block_population_capacity proj γ x S is the supremum (sSup) of the sum of p over S for all p in thermally_reachable_block_populations proj γ x.
-/

/-- The operational block population capacity concentrates maximal population on a subset of energy levels under thermal operations. -/
noncomputable def block_population_capacity {n m : ℕ} (proj : Fin n → Fin m) (γ x : Fin n → ℝ) (S : Finset (Fin m)) : ℝ := sSup ((fun p => ∑ k ∈ S, p k) '' thermally_reachable_block_populations proj γ x)
