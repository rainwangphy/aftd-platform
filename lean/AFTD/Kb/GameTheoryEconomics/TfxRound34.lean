import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TfxBval
import AFTD.Kb.GameTheoryEconomics.TfxAlphaEFXAt
import AFTD.Kb.GameTheoryEconomics.TfxVal

/-!
# tfx_round3_4

Topic: fair_division   Node: c7e518a0ee8c

Round 3 of the counterexample after rounds 1–2 allocations 0, 0, 1 and 0, 1, 0: every allocation of the third round violates α-EFX.
-/

open Finset in
/-- Round 3 of the counterexample after rounds 1–2 allocations `0, 0, 1` and `0, 1, 0`: every allocation of the third round violates `α`-EFX. -/
lemma tfx_round3_4 (α x : ℝ) (hα0 : 0 < α) (hx0 : 0 < x) (h1 : 2 < α * x)
    (h2 : 2 + x < 2 * (α * x)) (h3 : x < 2 * α + α * x)
    (a20 a21 a22 : Fin 2)
    (d2 : tfx_alphaEFXAt α (tfx_val x) (![![0, 0, 1], ![0, 1, 0], ![a20, a21, a22]] : Fin 3 → Fin 3 → Fin 2) 2) : False := by
  unfold tfx_alphaEFXAt at d2
  simp only [Fin.forall_fin_two, Fin.forall_fin_succ, Fin.forall_fin_one] at d2
  fin_cases a20 <;> fin_cases a21 <;> fin_cases a22 <;>
  (simp [tfx_bval, tfx_val, Fin.sum_univ_three] at d2 <;> linarith)
