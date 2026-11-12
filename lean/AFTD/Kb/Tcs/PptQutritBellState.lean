import AFTD.Prelude
import AFTD.Kb.Tcs.PptQutritBellVector

/-!
# ppt_qutrit_bell_state

Topic: quantum   Node: 15692f124145

Provenance: helper lemma. Helper for OP-693 from arXiv:1405.4502, equations (1), (2), (5); and arXiv:2010.04048, Appendix A.

The explicit two-qutrit positive-partial-transpose state in the Bell-violation example.
-/

open Matrix
open scoped BigOperators ComplexOrder

noncomputable def ppt_qutrit_bell_state : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ := ∑ l : Fin 4, (if l = 0 then (3257/6884 : ℝ) else if l = 3 then 27/6884 else 450/1721) •
    vecMulVec (ppt_qutrit_bell_vector l) (star (ppt_qutrit_bell_vector l))
