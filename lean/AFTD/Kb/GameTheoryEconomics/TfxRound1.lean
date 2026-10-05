import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TfxBval
import AFTD.Kb.GameTheoryEconomics.TfxAlphaEFXAt
import AFTD.Kb.GameTheoryEconomics.TfxVal

/-!
# tfx_round1

Topic: fair_division   Node: 6eda0be76971

Round 1 of the counterexample: the agent receiving b must receive nothing else.
-/

open Finset in
/-- Round 1 of the counterexample: the agent receiving `b` must receive nothing else. -/
lemma tfx_round1 (α x : ℝ) (hα0 : 0 < α) (hx0 : 0 < x) (h1 : 2 < α * x)
    (h2 : 2 + x < 2 * (α * x)) (h3 : x < 2 * α + α * x)
    (a00 a01 a02 a10 a11 a12 a20 a21 a22 : Fin 2)
    (d0 : tfx_alphaEFXAt α (tfx_val x) (![![a00, a01, a02], ![a10, a11, a12], ![a20, a21, a22]] : Fin 3 → Fin 3 → Fin 2) 0) :
    (a00 = 1 ∧ a01 = 1 ∧ a02 = 0) ∨ (a00 = 0 ∧ a01 = 0 ∧ a02 = 1) := by
  unfold tfx_alphaEFXAt at d0
  simp only [Fin.forall_fin_two, Fin.forall_fin_succ, Fin.forall_fin_one] at d0
  fin_cases a00 <;> fin_cases a01 <;> fin_cases a02 <;>
  first | (simp; done) | (exfalso; simp [tfx_bval, tfx_val, Fin.sum_univ_three] at d0 <;> linarith)
