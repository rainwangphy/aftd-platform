import AFTD.Prelude
import AFTD.Kb.Tcs.CssQuasiTransversalCczCode
import AFTD.Kb.Tcs.NotCampbellHowardConditionsZero
import AFTD.Kb.Tcs.CampbellHowardConditions
import AFTD.Kb.Tcs.CssZDistanceGeThree

/-!
# not_css_quasi_transversal_ccz_code_zero

Topic: quantum   Node: ec5e87a70576

Provenance: helper lemma. arXiv:2610.09341 Table 1

The zero logical and stabilizer matrices over ZMod 2 do not form a CSS quasi-transversal CCZ code of any block length n and stabilizer rank s.
-/

/-- Zero matrices do not satisfy the CSS quasi-transversal CCZ conditions. -/
theorem not_css_quasi_transversal_ccz_code_zero (n s : ℕ) :
    ¬ css_quasi_transversal_ccz_code n s 0 0 := by
  intro h
  exact not_campbell_howard_conditions_zero s n h.2
