import AFTD.Prelude

/-!
# is_strongly_matchable

Topic: elementary_number_theory   Node: d2074ad1fc00

Provenance: formalization of a published result. Source: arXiv:2610.37512 Section 1

A natural number n is strongly matchable if for every pair of natural numbers a and b with 0 < b and Nat.Coprime a b, there exists an equivalence e : Fin (Nat.divisors n).card ≃ Nat.divisors n such that (e i : ℕ) and a + b * (i : ℕ) are coprime for all i : Fin (Nat.divisors n).card.
-/

/-- A positive integer n is strongly matchable if its positive divisor set admits a coprime matching with every primitive arithmetic progression of length tau(n). -/
def is_strongly_matchable (n : ℕ) : Prop := ∀ (a b : ℕ), 0 < b → Nat.Coprime a b →
  ∃ e : Fin (Nat.divisors n).card ≃ Nat.divisors n,
    ∀ i : Fin (Nat.divisors n).card, Nat.Coprime (e i : ℕ) (a + b * (i : ℕ))
