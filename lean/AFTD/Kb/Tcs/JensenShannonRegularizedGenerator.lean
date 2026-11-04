import AFTD.Prelude
import AFTD.Kb.Tcs.JensenShannonGenerator

/-!
# jensen_shannon_regularized_generator

Topic: information   Node: 4a0f4fbdf79b

Provenance: formalization of a published result. Source: arXiv:2610.21231, Section II, Example 1(3)

The regularized generator with parameter c is f_c(x) = f_{JS}(x) + c x log x.
-/

/-- The regularized generator obtained by adding c times the Shannon information generator x log x to the Jensen-Shannon generator. -/
noncomputable def jensen_shannon_regularized_generator (c x : ℝ) : ℝ := jensen_shannon_generator x + c * (x * Real.log x)
