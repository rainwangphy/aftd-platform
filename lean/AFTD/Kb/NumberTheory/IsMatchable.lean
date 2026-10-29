import AFTD.Prelude

/-!
# is_matchable

Topic: elementary_number_theory   Node: d07d5435cf24

Provenance: formalization of a published result. Source: arXiv:2610.37512, Section 1

A natural number n is matchable if there exists an equivalence e : Fin (Nat.divisors n).card ≃ Nat.divisors n such that (e i : ℕ) and (i : ℕ) + 1 are coprime for all i : Fin (Nat.divisors n).card.
-/

/-- A natural number n is matchable if D(n) admits a coprime matching with {1, 2, ..., tau(n)}. -/
def is_matchable (n : ℕ) : Prop := ∃ e : Fin (Nat.divisors n).card ≃ Nat.divisors n,
    ∀ i : Fin (Nat.divisors n).card, Nat.Coprime (e i : ℕ) ((i : ℕ) + 1)
