import AFTD.Prelude
import AFTD.Kb.Tcs.PptQutritBellState
import AFTD.Kb.Tcs.PptQutritBellSetting

/-!
# ppt_qutrit_steered_unnormalized_effect

Topic: quantum   Node: 716b1c3a62a6

Provenance: helper lemma. Helper for OP-693 from arXiv:1405.4502, equations (1), (2), (5); and arXiv:2010.04048, Appendix A.

The unnormalized conditional operator on the second qutrit produced by the corresponding first-qutrit binary effect.
-/

open Matrix
open scoped BigOperators ComplexOrder

noncomputable def ppt_qutrit_steered_unnormalized_effect (j : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ := let A := vecMulVec (ppt_qutrit_bell_setting j) (star (ppt_qutrit_bell_setting j))
  fun x y => ∑ a : Fin 3, ∑ b : Fin 3, ppt_qutrit_bell_state (a,x) (b,y) * A b a
