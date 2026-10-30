import AFTD.Prelude
import AFTD.Kb.NumberTheory.RecurrenceBMap

/-!
# recurrence_b_map_zero

Topic: elementary_number_theory   Node: c2aca5a7758b

Provenance: helper lemma. arXiv:2610.34300 Proposition 7

The state transition map of recurrence (B) on (ℤ/3ℤ)^k maps the zero vector to the zero vector.
-/

/-- The zero state is mapped to zero under recurrence B. -/
theorem recurrence_b_map_zero (k : ℕ) : recurrence_b_map k 0 = 0 := by
  ext i
  simp [recurrence_b_map]
