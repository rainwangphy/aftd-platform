import AFTD.Prelude
import AFTD.Kb.Tcs.GaleSigmaThree
import AFTD.Kb.Tcs.GaleDistanceGraph

/-!
# is_gale_counterexample_three

Topic: combinatorics   Node: 8474c3514883

Provenance: formalization of a published result. Source: arXiv:2610.28828, Sec. 2 and Theorem 2

A finite subset V of the 3-dimensional Euclidean space `EuclideanSpace ℝ (Fin 3)` is a counterexample to Gale's conjecture in dimension 3 if it has strictly positive diameter and its distance threshold graph at threshold `gale_sigma_three * Metric.diam (V : Set (EuclideanSpace ℝ (Fin 3)))` is not 4-colorable.
-/

/-- Predicate asserting that a finite subset of R^3 is a counterexample to Gale's conjecture. -/
def is_gale_counterexample_three (V : Finset (EuclideanSpace ℝ (Fin 3))) : Prop := 0 < Metric.diam (V : Set (EuclideanSpace ℝ (Fin 3))) ∧
  ¬ (gale_distance_graph V (gale_sigma_three * Metric.diam (V : Set (EuclideanSpace ℝ (Fin 3))))).Colorable 4
