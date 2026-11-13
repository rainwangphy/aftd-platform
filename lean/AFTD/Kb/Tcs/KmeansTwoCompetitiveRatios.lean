import AFTD.Prelude
import AFTD.Kb.Tcs.KmeansOptTwo
import AFTD.Kb.Tcs.KmeansPlusPlusTwoExpectedCost

/-!
# kmeans_two_competitive_ratios

Topic: algorithms   Node: a71d7ee1717b

Provenance: formalization of a published result. Source: arXiv:2611.14573 Section 1.1

The set of 2-means competitive ratios is the collection of all real numbers r for which there exists a dimension d and a finite set X in Euclidean space R^d with OPT₂(X) > 0 such that r = E[Phi₂]/OPT₂(X).
-/

/-- The set of competitive ratios E[Phi₂] / OPT₂(X) achieved by k-means++ on finite sets X in Euclidean spaces with OPT₂(X) > 0. -/
def kmeans_two_competitive_ratios : Set ℝ := { r : ℝ | ∃ (d : ℕ) (X : Finset (EuclideanSpace ℝ (Fin d))), 0 < kmeans_opt_two X ∧ r = kmeans_plus_plus_two_expected_cost X / kmeans_opt_two X }
