import AFTD.Prelude
import AFTD.Kb.Tcs.ComparisonAlgorithm
import AFTD.Kb.Tcs.LinearOrderMin

/-!
# comparison_algorithm_success_prob

Topic: quantum   Node: ac863a9f4ba2

Provenance: formalization of a published result. Source: arXiv:2610.34762 Section 2 (equation 2)

The probability that a comparison algorithm A on n objects selects the minimum element under linear order L.
-/

/-- The probability that comparison algorithm `A` selects the minimum element under linear order `L`. -/
def comparison_algorithm_success_prob {n : ℕ} {c : ℕ} (hn : 0 < n)
    (A : ComparisonAlgorithm n c) (L : LinearOrder (Fin n)) : ℝ :=
  A.prob L (linearOrderMin hn L)
