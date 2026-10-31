import AFTD.Prelude
import AFTD.Kb.Optimization.ThermallyReachableMicro
import AFTD.Kb.Optimization.FiberSumVec

/-!
# thermally_reachable_block_populations

Topic: submodular   Node: 08fe99b5640b

Provenance: formalization of a published result. Source: arXiv:2610.35433:146

Given a block-assignment map proj from Fin n to Fin m and vectors γ, x : Fin n → ℝ, thermally_reachable_block_populations proj γ x is the set of vectors p : Fin m → ℝ such that there exists x' ∈ stdSimplex ℝ (Fin n) satisfying thermally_reachable_micro γ x x' and p = fiber_sum_vec proj x'.
-/

/-- The set of block population vectors reachable from an initial microstate distribution under thermal operations. -/
def thermally_reachable_block_populations {n m : ℕ} (proj : Fin n → Fin m) (γ x : Fin n → ℝ) : Set (Fin m → ℝ) := { p | ∃ x' ∈ stdSimplex ℝ (Fin n), thermally_reachable_micro γ x x' ∧ p = fiber_sum_vec proj x' }
