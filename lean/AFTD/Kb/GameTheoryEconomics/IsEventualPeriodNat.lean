import AFTD.Prelude

/-!
# is_eventual_period_nat

Topic: combinatorial_games   Node: 058075737320

Provenance: formalization of a published result. Source: arXiv:2611.31336

A positive integer p is an eventual period of a sequence g : ℕ → ℕ of natural numbers if there exists N : ℕ such that g (n + p) = g n for all n ≥ N.
-/

/-- Predicate that p is an eventual period of a sequence of natural numbers. -/
def is_eventual_period_nat (g : ℕ → ℕ) (p : ℕ) : Prop := 0 < p ∧ ∃ N : ℕ, ∀ n ≥ N, g (n + p) = g n
