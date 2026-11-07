import AFTD.Prelude
import AFTD.Kb.Tcs.DrfProp1Alg
import AFTD.Kb.Tcs.DrfProp1OptBound

/-!
# drf_prop1_ratio

Topic: online_algorithms   Node: 21285d03652b

Provenance: formalization of a published result. Source: arXiv:2611.07905 Proposition 1

For two natural numbers D and m, `drf_prop1_ratio D m` is defined as the real number `drf_prop1_alg D m / drf_prop1_opt_bound D m`.
-/

/-- Ratio of DRF completion time to the offline completion time bound for the lower-bound instance. -/
noncomputable def drf_prop1_ratio (D m : ℕ) : ℝ := drf_prop1_alg D m / drf_prop1_opt_bound D m
