import AFTD.Prelude
import AFTD.Kb.NumberTheory.IsMNumber

/-!
# is_m_number_of_dvd

Topic: elementary_number_theory   Node: 7a877ee6bb6f

Provenance: helper lemma. arXiv:2610.37512, Section 6

If n is an M-number and d divides n, then d is an M-number.
-/

/-- Any divisor of an M-number is also an M-number. -/
theorem is_m_number_of_dvd {n d : ℕ} (h : is_m_number n) (hd : d ∣ n) : is_m_number d := fun p hp hpd => h p hp (dvd_trans hpd hd)
