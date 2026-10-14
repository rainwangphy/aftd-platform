import AFTD.Prelude
import AFTD.Kb.NumberTheory.NatLeastPrimeNotDvd

/-!
# davenport_box_extremal_sequence

Topic: elementary_number_theory   Node: 9ce401bb47e8

Provenance: formalization of a published result. Source: arXiv:2610.16562 (The Davenport constant of low-dimensional boxes), Sec. 2 (the sequence S(m), before Theorem 1).

The sequence S(m): q(m)(m−1)+m copies of (m, m), 2m² − m·q(m) copies of (−m, m−1), and 2m² − m copies of (m − q(m), −m).
-/

/-- The sequence `S(m)` of arXiv:2610.16562. -/
noncomputable def davenport_box_extremal_sequence (m : ℕ) : Multiset (ℤ × ℤ) :=
  Multiset.replicate (nat_least_prime_not_dvd m * (m - 1) + m) ((m : ℤ), (m : ℤ)) +
    Multiset.replicate (2 * m ^ 2 - m * nat_least_prime_not_dvd m) (-(m : ℤ), (m : ℤ) - 1) +
    Multiset.replicate (2 * m ^ 2 - m) ((m : ℤ) - nat_least_prime_not_dvd m, -(m : ℤ))
