import AFTD.Prelude
import AFTD.Kb.Physics.EnergyFilterSequenceLatticeS4
import AFTD.Kb.Physics.EnergyFilterQuarticCycleTsumEqS4
import AFTD.Kb.Physics.EnergyFilterQuarticTannery

/-!
# energy_filter_quartic_tannery_to_s4

Topic: statistical_mechanics   Node: 30f2f5d09ab8

Provenance: helper lemma. OP-892: shifted quartic reindexing and dominated convergence.

If the absolute quartic cycle and each convolution are summable, a uniformly bounded shifted kernel with a common pointwise limit converges after cycle summation to that limit times the lattice convolution-square constant.
-/

theorem energy_filter_quartic_tannery_to_s4
    (a : ℤ → ℝ) (K : ℕ → ℤ → ℤ → ℤ → ℝ) (c C : ℝ) (hC : 0 ≤ C)
    (hab : Summable (fun p : ℤ × ℤ × ℤ =>
      |a p.1 * a p.2.1 * a p.2.2 * a (p.1 - p.2.1 + p.2.2)|))
    (hconv : ∀ m : ℤ, Summable (fun j : ℤ => a j * a (m - j)))
    (hlim : ∀ u v w, Filter.Tendsto (fun k => K k u v w) Filter.atTop (nhds c))
    (hbound : ∀ᶠ k in Filter.atTop, ∀ u v w, |K k u v w| ≤ C) :
    Filter.Tendsto
      (fun k : ℕ => ∑' p : ℤ × ℤ × ℤ,
        (a p.1 * a p.2.1 * a p.2.2 * a (p.1 - p.2.1 + p.2.2)) *
          K k p.1 p.2.1 (p.2.1 - p.2.2))
      Filter.atTop (nhds (energy_filter_sequence_lattice_s4 a * c)) := by
  have ht := energy_filter_quartic_tannery a K c C hC hab hlim hbound
  rw [energy_filter_quartic_cycle_tsum_eq_s4 a hab hconv] at ht
  exact ht
