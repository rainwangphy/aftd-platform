import AFTD.Prelude
import AFTD.Kb.Optimization.IsGibbsStochastic

/-!
# thermally_reachable_micro

Topic: submodular   Node: df256c78e0ef

Provenance: formalization of a published result. Source: arXiv:2610.35433:135

A microstate distribution x' on n energy levels is thermally reachable from an initial distribution x with respect to the Gibbs vector γ if there exists a Gibbs-stochastic matrix T such that x' = T x.
-/

/-- A microstate probability vector is thermally reachable from another under equilibrium distribution γ if connected by a Gibbs-stochastic matrix. -/
def thermally_reachable_micro {n : ℕ} (γ x x' : Fin n → ℝ) : Prop := ∃ T : Fin n → Fin n → ℝ, is_gibbs_stochastic γ T ∧ (∀ i, x' i = ∑ j, T i j * x j)
