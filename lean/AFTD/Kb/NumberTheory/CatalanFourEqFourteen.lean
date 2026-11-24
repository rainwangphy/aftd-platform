import AFTD.Prelude

/-!
# catalan_four_eq_fourteen

Topic: elementary_number_theory   Node: 1c34a49b92e0

Provenance: helper lemma. folklore

The fourth Catalan number equals 14.
-/

/-- The fourth Catalan number is 14. -/
theorem catalan_four_eq_fourteen : catalan 4 = 14 := by
  rw [catalan_eq_centralBinom_div]
  decide
