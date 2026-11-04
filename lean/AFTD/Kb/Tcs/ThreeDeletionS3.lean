import AFTD.Prelude

/-!
# three_deletion_S3

Topic: information   Node: da890fe95c71

Provenance: formalization of a published result. Source: arXiv:2611.01064 Eq. 21

For n ≥ 1, three_deletion_S3 n is 3 * n * f 2 + 2 * n * f 3 + n^2 * f 4 + n * (n - 1) * f 6 + Nat.choose n 3 * f 8 + n * f (2 * n) + 2 * f (2 * n + 1) + 2 * f (n + 1), where f t = if t = 0 then 0 else t * Real.logb 2 t.
-/

/-- Entropy correction sum S_3(n) for the three-deletion channel on alternating inputs. -/
noncomputable def three_deletion_S3 (n : ℕ) : ℝ :=
  let f : ℝ → ℝ := fun t => if t = 0 then 0 else t * Real.logb 2 t
  3 * (n : ℝ) * f 2 + 2 * (n : ℝ) * f 3 + (n : ℝ) ^ 2 * f 4 + ((n * (n - 1) : ℕ) : ℝ) * f 6 +
  ((n.choose 3 : ℕ) : ℝ) * f 8 + (n : ℝ) * f (2 * (n : ℝ)) + 2 * f (2 * (n : ℝ) + 1) + 2 * f ((n : ℝ) + 1)
