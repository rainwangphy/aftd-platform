import AFTD.Prelude

/-!
# plurality_regularization_threshold

Topic: social_choice   Node: c2416fad6318

Provenance: formalization of a published result. Source: OP-799

For numbers of voters n and candidates m, plurality_regularization_threshold n m is 1 / ((m - 2 : ℝ) * n - 2 * m).
-/

/-- The exact regularization threshold 1 / ((m - 2) * n - 2 * m) for n voters and m candidates. -/
noncomputable def plurality_regularization_threshold (n m : ℕ) : ℝ := 1 / ((m - 2 : ℝ) * n - 2 * m)
