import AFTD.Prelude

/-!
# mu_star

Topic: combinatorial_games   Node: 49cefb8a60e5

Provenance: formalization of a published result. Source: arXiv:2611.05898, Definition 2.1

A natural number d satisfies mu_star if for every prime number p with p ≠ 2, p^2 does not divide d.
-/

/-- Predicate asserting that no square of an odd prime divides d. -/
def mu_star (d : ℕ) : Prop := ∀ p, Nat.Prime p → p ≠ 2 → ¬ (p^2 ∣ d)
