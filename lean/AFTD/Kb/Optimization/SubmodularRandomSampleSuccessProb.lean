import AFTD.Prelude
import AFTD.Kb.Optimization.SubmodularRandomSampleGuarantee

/-!
# submodular_random_sample_success_prob

Topic: submodular   Node: 638e06ee9abd

Provenance: formalization of a published result. Source: arXiv:2611.23637 Sec. 1.1, after Theorem 1.2

The probability under the uniform product distribution on (2^{{0,...,n-1}})^t that an independent random sample of t subsets achieves the gamma-approximation guarantee for all non-negative submodular functions.
-/

/-- The probability that a uniformly random sample of t independent subsets achieves the gamma-approximation guarantee for all non-negative submodular functions. -/
noncomputable def submodular_random_sample_success_prob (n t : ℕ) (γ : ℝ) : ℝ :=
  ((PMF.uniformOfFintype (Fin t → Finset (Fin n))).toMeasure
    {R | submodular_random_sample_guarantee R γ}).toReal
