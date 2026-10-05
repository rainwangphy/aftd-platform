import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TfxBval
import AFTD.Kb.GameTheoryEconomics.TfxAlphaEFXAt
import AFTD.Kb.GameTheoryEconomics.TfxVal

/-!
# tfx_round2B

Topic: fair_division   Node: d5c16a0e9aad

Round 2 of the counterexample after round-1 allocation 0, 0, 1.
-/

open Finset in
/-- Round 2 of the counterexample after round-1 allocation `0, 0, 1`. -/
lemma tfx_round2B (α x : ℝ) (hα0 : 0 < α) (hx0 : 0 < x) (h1 : 2 < α * x)
    (h2 : 2 + x < 2 * (α * x)) (h3 : x < 2 * α + α * x)
    (a10 a11 a12 a20 a21 a22 : Fin 2)
    (d1 : tfx_alphaEFXAt α (tfx_val x) (![![0, 0, 1], ![a10, a11, a12], ![a20, a21, a22]] : Fin 3 → Fin 3 → Fin 2) 1) :
    (a10 = 1 ∧ a11 = 1 ∧ a12 = 0) ∨ (a10 = 0 ∧ a11 = 1 ∧ a12 = 0) := by
  unfold tfx_alphaEFXAt at d1
  simp only [Fin.forall_fin_two, Fin.forall_fin_succ, Fin.forall_fin_one] at d1
  fin_cases a10 <;> fin_cases a11 <;> fin_cases a12 <;>
  first | (simp; done) | (exfalso; simp [tfx_bval, tfx_val, Fin.sum_univ_three] at d1 <;> linarith)
