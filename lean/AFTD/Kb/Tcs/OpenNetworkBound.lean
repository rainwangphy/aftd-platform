import AFTD.Prelude

/-!
# open_network_bound

Topic: quantum   Node: 392d1b7e7c41

Provenance: formalization of a published result. Source: arXiv:2610.35838 Theorem 4, Eq. (26)

The function open_network_bound maps each natural number n to a real number, defined by cases: if n is even, it equals 2; otherwise (if n is odd), it equals (2 : ℝ) ^ (1 - 1 / (2 * (n : ℝ))).
-/

/-- Maximal quantum value bound for the open n-source network. -/
noncomputable def open_network_bound (n : ℕ) : ℝ := if Even n then 2 else (2 : ℝ) ^ (1 - 1 / (2 * (n : ℝ)))
