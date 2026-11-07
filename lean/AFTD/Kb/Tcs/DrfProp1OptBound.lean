import AFTD.Prelude
import AFTD.Kb.Tcs.DrfProp1K

/-!
# drf_prop1_opt_bound

Topic: online_algorithms   Node: 47121241066d

Provenance: formalization of a published result. Source: arXiv:2611.07905 Proposition 1

For two natural numbers D and m, `drf_prop1_opt_bound D m` is defined as the real number `(D : ℝ) * (m : ℝ) * ((m : ℝ) + 1) / 2 + (m : ℝ) * (drf_prop1_k D m : ℝ) + (drf_prop1_k D m : ℝ) * ((drf_prop1_k D m : ℝ) + 1) / 2`.
-/

/-- Offline schedule total completion time bound for the lower-bound instance with D resources and parameter m. -/
noncomputable def drf_prop1_opt_bound (D m : ℕ) : ℝ := (D : ℝ) * (m : ℝ) * ((m : ℝ) + 1) / 2 + (m : ℝ) * (drf_prop1_k D m : ℝ) + (drf_prop1_k D m : ℝ) * ((drf_prop1_k D m : ℝ) + 1) / 2
