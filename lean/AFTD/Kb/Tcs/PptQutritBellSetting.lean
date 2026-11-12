import AFTD.Prelude

/-!
# ppt_qutrit_bell_setting

Topic: quantum   Node: ae74a3cd19ef

Provenance: helper lemma. Helper for OP-693 from arXiv:1405.4502, equations (1), (2), (5); and arXiv:2010.04048, Appendix A.

The three unit vectors defining the binary projective settings in the Bell example.
-/

open Matrix
open scoped BigOperators ComplexOrder

noncomputable def ppt_qutrit_bell_setting (j : Fin 3) : Fin 3 → ℂ := if j = 0 then ![-(1/5 : ℂ), (Real.sqrt 3 : ℂ)/5, (Real.sqrt 21 : ℂ)/5]
  else if j = 1 then ![(2/5 : ℂ), 0, (Real.sqrt 21 : ℂ)/5]
  else ![-(1/5 : ℂ), -(Real.sqrt 3 : ℂ)/5, (Real.sqrt 21 : ℂ)/5]
