import AFTD.Prelude

/-!
# arithmetic_fourier_bound

Topic: elementary_number_theory   Node: b1d57abf49f7

Provenance: formalization of a published result. Source: arXiv:2610.38447, Section 5.3, eq. (35)

For odd dimension d, lambda_d is the least positive integer n satisfying n = 2 mod 3 and 8(2^d - 1) + 2n + 9 * 1_{n odd} <= 3n^2.
-/

/-- The arithmetic lower bound lambda_d on the Fourier threshold nu(d) for odd d. -/
noncomputable def arithmetic_fourier_bound (d : ℕ) : ℕ :=
  sInf {n : ℕ | n % 3 = 2 ∧ 8 * (2^d - 1) + 2 * n + (if n % 2 = 1 then 9 else 0) ≤ 3 * n^2}
