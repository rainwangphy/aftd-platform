import AFTD.Prelude

/-!
# closed_network_bound

Topic: quantum   Node: d34d5a639fc5

Provenance: formalization of a published result. Source: arXiv:2610.35838 Theorem 4, Eq. (25)

The function closed_network_bound maps each natural number n to a real number, defined by cases: if n is even, it equals Real.sqrt 2; otherwise (if n is odd), it equals (2 : ℝ) ^ ((1 : ℝ) / 2 - 1 / (2 * (n : ℝ))).
-/

/-- Maximal quantum value bound for the closed n-source network. -/
noncomputable def closed_network_bound (n : ℕ) : ℝ := if Even n then Real.sqrt 2 else (2 : ℝ) ^ ((1 : ℝ) / 2 - 1 / (2 * (n : ℝ)))
