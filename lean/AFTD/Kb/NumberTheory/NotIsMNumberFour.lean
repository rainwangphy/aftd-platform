import AFTD.Prelude
import AFTD.Kb.NumberTheory.IsMNumber

/-!
# not_is_m_number_four

Topic: elementary_number_theory   Node: d7c6cf51b080

Provenance: helper lemma. arXiv:2610.37512 Section 6

The natural number 4 is not an M-number.
-/

/-- The integer 4 is not an M-number. -/
theorem not_is_m_number_four : ¬ is_m_number 4 := fun h => h 2 Nat.prime_two dvd_rfl
