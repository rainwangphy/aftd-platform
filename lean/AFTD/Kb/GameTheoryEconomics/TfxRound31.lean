import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TfxBval
import AFTD.Kb.GameTheoryEconomics.TfxAlphaEFXAt
import AFTD.Kb.GameTheoryEconomics.TfxVal

/-!
# tfx_round3_1

Topic: fair_division   Node: 30ae7a7b44cb

Round 3 of the counterexample after rounds 1–2 allocations 1, 1, 0 and 1, 0, 1: every allocation of the third round violates α-EFX.
-/

open Finset in
/-- Round 3 of the counterexample after rounds 1–2 allocations `1, 1, 0` and `1, 0, 1`: every allocation of the third round violates `α`-EFX. -/
lemma tfx_round3_1 (α x : ℝ) (hα0 : 0 < α) (hx0 : 0 < x) (h1 : 2 < α * x)
    (h2 : 2 + x < 2 * (α * x)) (h3 : x < 2 * α + α * x)
    (a20 a21 a22 : Fin 2)
    (d2 : tfx_alphaEFXAt α (tfx_val x) (![![1, 1, 0], ![1, 0, 1], ![a20, a21, a22]] : Fin 3 → Fin 3 → Fin 2) 2) : False := by
  unfold tfx_alphaEFXAt at d2
  simp only [Fin.forall_fin_two, Fin.forall_fin_succ, Fin.forall_fin_one] at d2
  fin_cases a20 <;> fin_cases a21 <;> fin_cases a22 <;>
  (simp [tfx_bval, tfx_val, Fin.sum_univ_three] at d2 <;> linarith)
