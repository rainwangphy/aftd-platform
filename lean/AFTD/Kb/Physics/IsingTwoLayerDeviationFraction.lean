import AFTD.Prelude
import AFTD.Kb.Physics.IsingRegularPairBase

/-!
# ising_two_layer_deviation_fraction

Topic: statistical_mechanics   Node: 7bf7bdd44f3a

Provenance: helper lemma. step towards critical_regular_ising_two_layer_weak_matching_quartic_crossover

The fraction of ordered pairs of d-regular graphs on Fin n on which |Φ p| is at least ε; the general form of the two-layer bad fraction for an arbitrary real observable Φ of a graph pair.
-/

/-- Fraction of regular pairs on which |Φ| ≥ ε; general form of the bad fraction. -/
noncomputable def ising_two_layer_deviation_fraction (d n : ℕ) (ε : ℝ) (Φ : SimpleGraph (Fin n) × SimpleGraph (Fin n) → ℝ) : ℝ := (((ising_regular_pair_base d n).filter (fun p => ε ≤ |Φ p|)).card : ℝ) / ((ising_regular_pair_base d n).card : ℝ)
