import AFTD.Prelude
import AFTD.Kb.NumberTheory.IsMNumber

/-!
# is_m_number_one

Topic: elementary_number_theory   Node: 14e21b4bffa2

Provenance: helper lemma. arXiv:2610.37512 Section 1

The natural number 1 is an M-number.
-/

/-- The integer 1 is an M-number. -/
theorem is_m_number_one : is_m_number 1 := by
  intro p hp hdiv
  have h1 : p ^ p = 1 := Nat.eq_one_of_dvd_one hdiv
  have h2 : 1 < p := hp.two_le
  have h3 : 1 < p ^ p := Nat.one_lt_pow (by omega) h2
  omega
