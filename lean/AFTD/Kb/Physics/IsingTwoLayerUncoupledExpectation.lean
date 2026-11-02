import AFTD.Prelude
import AFTD.Kb.Physics.IsingSingleLayerGibbsWeight

/-!
# ising_two_layer_uncoupled_expectation

Topic: statistical_mechanics   Node: 960a3bb49064

Provenance: helper lemma. step towards critical_regular_ising_two_layer_weak_matching_quartic_crossover

The expectation of an observable F of the spin pair under the product of the two single-layer Gibbs measures — the uncoupled reference measure E_0 of the two-layer system.
-/

/-- Uncoupled expectation E_0[F] under the product of the two single-layer Gibbs laws. -/
noncomputable def ising_two_layer_uncoupled_expectation (d n : ℕ) (G H : SimpleGraph (Fin n)) (F : (Fin n → Bool) → (Fin n → Bool) → ℝ) : ℝ := (∑ σ : Fin n → Bool, ∑ τ : Fin n → Bool, ising_single_layer_gibbs_weight d n G σ * ising_single_layer_gibbs_weight d n H τ * F σ τ) / (∑ σ : Fin n → Bool, ∑ τ : Fin n → Bool, ising_single_layer_gibbs_weight d n G σ * ising_single_layer_gibbs_weight d n H τ)
