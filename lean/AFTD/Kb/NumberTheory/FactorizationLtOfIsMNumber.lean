import AFTD.Prelude
import AFTD.Kb.NumberTheory.IsMNumber

/-!
# factorization_lt_of_is_m_number

Topic: elementary_number_theory   Node: 466da83bcb71

Provenance: helper lemma. step towards strongly_matchable_of_is_m_number

If n is a positive M-number and p is prime, then n.factorization p < p.
-/

/-- If a positive integer n is an M-number, then its p-adic valuation at any prime p is strictly less than p. -/
theorem factorization_lt_of_is_m_number (n : ℕ) (hn : 0 < n) (hm : is_m_number n) (p : ℕ) (hp : p.Prime) :
    n.factorization p < p := by
  by_contra h
  have hp_le : p ≤ n.factorization p := Nat.le_of_not_lt h
  exact hm p hp
    ((Nat.Prime.pow_dvd_iff_le_factorization hp (Nat.pos_iff_ne_zero.mp hn)).mpr hp_le)
