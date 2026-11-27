import AFTD.Prelude

/-!
# blackburn_capacity

Topic: information   Node: c729db0e278d

Provenance: formalization of a published result. Source: arXiv:2611.28776, Eq. (1)

The Blackburn capacity constant c_n is ((n - 1) / n)^(n - 1) / n for each n.
-/

/-- The Levenshtein-Blackburn capacity constant c_n = ((n-1)/n)^(n-1) / n for length-n codes. -/
noncomputable def blackburn_capacity (n : ℕ) : ℝ := ((n - 1 : ℝ) / n) ^ (n - 1) / (n : ℝ)
