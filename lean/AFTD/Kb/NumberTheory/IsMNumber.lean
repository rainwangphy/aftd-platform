import AFTD.Prelude

/-!
# is_m_number

Topic: elementary_number_theory   Node: 736d811cf81f

Provenance: formalization of a published result. Source: arXiv:2610.37512 Section 1

A natural number n is an M-number if for every prime p, p^p does not divide n.
-/

/-- An integer n is an M-number if p^p does not divide n for every prime p. -/
def is_m_number (n : ℕ) : Prop := ∀ p : ℕ, p.Prime → ¬ p ^ p ∣ n
