import AFTD.Prelude

/-!
# ising_regular_pair_base

Topic: statistical_mechanics   Node: 2cc2596146c9

Provenance: helper lemma. step towards critical_regular_ising_two_layer_weak_matching_quartic_crossover

The finite set of ordered pairs of simple d-regular graphs on Fin n, the common base over which every bad fraction is taken.
-/

/-- Ordered pairs of d-regular graphs on Fin n; common base of every bad fraction. -/
noncomputable def ising_regular_pair_base (d n : ℕ) : Finset (SimpleGraph (Fin n) × SimpleGraph (Fin n)) := by
  classical
  exact Finset.univ.filter (fun p => p.1.IsRegularOfDegree d ∧ p.2.IsRegularOfDegree d)
