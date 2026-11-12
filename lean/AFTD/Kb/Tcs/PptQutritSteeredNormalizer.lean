import AFTD.Prelude

/-!
# ppt_qutrit_steered_normalizer

Topic: quantum   Node: 3671d233146b

Provenance: helper lemma. Helper for OP-693 from arXiv:1405.4502, equations (1), (2), (5); and arXiv:2010.04048, Appendix A.

The diagonal inverse square root of the second-qutrit reduced state.
-/

open Matrix
open scoped BigOperators ComplexOrder

noncomputable def ppt_qutrit_steered_normalizer : Matrix (Fin 3) (Fin 3) ℂ := diagonal fun i => if i = 2 then (Real.sqrt (6884 / 10 : ℝ) : ℂ) else (Real.sqrt (6884 / 3437 : ℝ) : ℂ)
