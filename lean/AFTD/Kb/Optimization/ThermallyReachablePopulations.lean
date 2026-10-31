import AFTD.Prelude
import AFTD.Kb.Optimization.ThermallyReachableBlockPopulations

/-!
# thermally_reachable_populations

Topic: submodular   Node: 4cef2870d0d0

Provenance: formalization of a published result. Source: arXiv:2610.35433 Eq. 3

Given a Gibbs vector γ and an initial distribution x on Fin n, the thermally reachable populations are the population vectors x' in the probability simplex that are thermally reachable from x with respect to γ.
-/

/-- Thermally reachable microstate populations: the set of probability vectors reachable from x under Gibbs-preserving stochastic operations with respect to Gibbs vector γ. -/
def thermally_reachable_populations {n : ℕ} (γ x : Fin n → ℝ) : Set (Fin n → ℝ) := thermally_reachable_block_populations id γ x
