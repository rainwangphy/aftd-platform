import AFTD.Prelude
import AFTD.Kb.Tcs.IntCrescentGaussian

/-!
# int_crescent_point

Topic: combinatorics   Node: 5b70758d1255

Provenance: formalization of a published result. Source: arXiv:2610.38368 Section 3

For a natural number n and an index j in Fin n, int_crescent_point n j is the integer vector of type Fin 3 → ℤ whose coordinate 0 is (int_crescent_gaussian n j).re, whose coordinate 1 is (int_crescent_gaussian n j).im, and whose coordinate 2 is 2 * (j : ℤ) * (4 * (n : ℤ)^2 + 1)^(n - 1).
-/

/-- The j-th integer-coordinate point in ℤ^3 of the n-point crescent configuration. -/
def int_crescent_point (n : ℕ) (j : Fin n) : Fin 3 → ℤ := fun i =>
  match i with
  | 0 => (int_crescent_gaussian n j).re
  | 1 => (int_crescent_gaussian n j).im
  | 2 => 2 * (j : ℤ) * (4 * (n : ℤ)^2 + 1) ^ (n - 1)
