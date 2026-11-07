import AFTD.Prelude
import AFTD.Kb.Tcs.DrfProp1K

/-!
# drf_prop1_alg

Topic: online_algorithms   Node: 661cc8cfbee1

Provenance: formalization of a published result. Source: arXiv:2611.07905 Proposition 1

Given two natural numbers D and m, `drf_prop1_alg D m` is defined as the real number `((D : ℝ) * (m : ℝ) + (drf_prop1_k D m : ℝ)) * ((m : ℝ) + (drf_prop1_k D m : ℝ))`.
-/

/-- Total completion time under Dominant Resource Fairness for the lower-bound instance with D resources and parameter m. -/
noncomputable def drf_prop1_alg (D m : ℕ) : ℝ := ((D : ℝ) * (m : ℝ) + (drf_prop1_k D m : ℝ)) * ((m : ℝ) + (drf_prop1_k D m : ℝ))
