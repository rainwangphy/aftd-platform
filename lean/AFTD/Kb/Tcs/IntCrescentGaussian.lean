import AFTD.Prelude

/-!
# int_crescent_gaussian

Topic: combinatorics   Node: 68bed6e51140

Provenance: formalization of a published result. Source: arXiv:2610.38368 Section 3

For a natural number n and an index j in Fin n, int_crescent_gaussian n j is the Gaussian integer of type GaussianInt given by the integer scalar (4 * (n : ℤ)^2 + 1)^(n - 1 - (j : ℕ)) multiplying the Gaussian integer ⟨4 * (n : ℤ)^2 - 1, 4 * (n : ℤ)⟩ raised to the natural power (j : ℕ).
-/

open scoped GaussianInt in
/-- Gaussian integer whose real and imaginary parts give the first two integer coordinates of the j-th point. -/
def int_crescent_gaussian (n : ℕ) (j : Fin n) : GaussianInt := ((4 * (n : ℤ)^2 + 1) ^ (n - 1 - (j : ℕ)) : ℤ) • (⟨4 * (n : ℤ)^2 - 1, 4 * (n : ℤ)⟩ ^ (j : ℕ))
