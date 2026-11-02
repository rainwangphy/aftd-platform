import AFTD.Prelude
import AFTD.Kb.Physics.IsingRingSpin

/-!
# ising_two_layer_tilt

Topic: statistical_mechanics   Node: ea4e4b0a6c29

Provenance: helper lemma. step towards critical_regular_ising_two_layer_weak_matching_quartic_crossover

The overlap tilt exp(c · n^{-1/2} · Σ_v σ_v τ_v) coupling the two spin layers, where σ_v, τ_v ∈ {±1} are the spins at vertex v.
-/

/-- Overlap tilt exp(c n^{-1/2} Σ_v σ_v τ_v) coupling the two layers. -/
noncomputable def ising_two_layer_tilt (n : ℕ) (c : ℝ) (σ τ : Fin n → Bool) : ℝ := Real.exp (c * (n : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ v, ising_ring_spin (σ v) * ising_ring_spin (τ v))
