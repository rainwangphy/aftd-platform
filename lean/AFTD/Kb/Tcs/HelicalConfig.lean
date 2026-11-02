import AFTD.Prelude
import AFTD.Kb.Tcs.HelicalPoint

/-!
# helical_config

Topic: combinatorics   Node: 12c00bdf77b6

Provenance: formalization of a published result. Source: arXiv:2610.38368, Theorem 1.1

For a natural number n, helical_config n is the finite set in EuclideanSpace ℝ (Fin 3) obtained as the image of Finset.univ under helical_point n.
-/

/-- The helical configuration of n points in EuclideanSpace ℝ (Fin 3). -/
noncomputable def helical_config (n : ℕ) : Finset (EuclideanSpace ℝ (Fin 3)) :=
  Finset.univ.image (helical_point n)
