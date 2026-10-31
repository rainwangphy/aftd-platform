import AFTD.Prelude

/-!
# minimal_advantage

Topic: combinatorics   Node: 2198fbcd630f

Provenance: formalization of a published result. Source: arXiv:2610.40321 Eq 1

The minimal winning advantage threshold for an n-sided die: n^2 / 2 + 1 if n is even, and (n^2 + 1) / 2 if n is odd.
-/

/-- Minimal winning advantage threshold for an n-sided die. -/
def minimal_advantage (n : ℕ) : ℕ := if n % 2 == 0 then n ^ 2 / 2 + 1 else (n ^ 2 + 1) / 2
