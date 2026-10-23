import AFTD.Prelude

/-!
# zonotope_polygon_S

Topic: graphs   Node: 810bfcf06161

Provenance: formalization of a published result. Source: arXiv:2610.14100 Proposition 1

For a natural number n, the zonotope polygon S_n is the set of all complex numbers of the form ∑_{m=1}^{n-1} t_m g_m with 0 ≤ t_m ≤ 1, where g_m = (1/n)(1 - exp(-2πi m/n)).
-/

/-- The zonotope polygon S_n formed by the Minkowski sum of segments [0, g_m] for m = 1, ..., n-1. -/
noncomputable def zonotope_polygon_S (n : ℕ) : Set ℂ := { z : ℂ | ∃ t : ℕ → ℝ, (∀ m ∈ Finset.Ico 1 n, 0 ≤ t m ∧ t m ≤ 1) ∧
    z = ∑ m ∈ Finset.Ico 1 n, (t m : ℂ) * ((1 / (n : ℂ)) * (1 - Complex.exp (-2 * Real.pi * Complex.I * (m : ℂ) / (n : ℂ)))) }
