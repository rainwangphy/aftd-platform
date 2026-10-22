import AFTD.Prelude

/-!
# four_point_set_interval_length

Topic: combinatorics   Node: 95117d1b9a66

Provenance: helper lemma. arXiv:2610.24281 Lemma 3.2

For an integer n, setting a = 2n - 1 and b = 2n + 1, the number of integers in the interval [a + 2b, ab - 1 - a - b], given by (ab - 1 - a - b) - (a + 2b) + 1, equals 4n^2 - 10n - 2.
-/

/-- The length of the interval [a + 2b, ab - 1 - a - b] equals 4n^2 - 10n - 2. -/
theorem four_point_set_interval_length (n : ℤ) :
    let a : ℤ := 2 * n - 1
    let b : ℤ := 2 * n + 1
    a * b - 1 - a - b - (a + 2 * b) + 1 = 4 * n ^ 2 - 10 * n - 2 := by
  intro a b
  ring
