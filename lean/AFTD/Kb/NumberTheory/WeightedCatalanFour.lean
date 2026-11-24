import AFTD.Prelude

/-!
# weighted_catalan_four

Topic: elementary_number_theory   Node: c61712f122c9

Provenance: formalization of a published result. Source: arXiv:2611.26953, Equation (1)

For a function b : ℕ → ℤ from natural numbers to integers, weighted_catalan_four b is defined as the integer b 0 ^ 4 + 3 * b 0 ^ 3 * b 1 + 3 * b 0 ^ 2 * b 1 ^ 2 + b 0 * b 1 ^ 3 + 2 * b 0 ^ 2 * b 1 * b 2 + 2 * b 0 * b 1 ^ 2 * b 2 + b 0 * b 1 * b 2 ^ 2 + b 0 * b 1 * b 2 * b 3.
-/

/-- The fourth weighted Catalan number expressed as an explicit polynomial for a sequence b : ℕ → ℤ. -/
def weighted_catalan_four (b : ℕ → ℤ) : ℤ :=
  b 0 ^ 4 + 3 * b 0 ^ 3 * b 1 + 3 * b 0 ^ 2 * b 1 ^ 2 + b 0 * b 1 ^ 3 +
  2 * b 0 ^ 2 * b 1 * b 2 + 2 * b 0 * b 1 ^ 2 * b 2 + b 0 * b 1 * b 2 ^ 2 +
  b 0 * b 1 * b 2 * b 3
