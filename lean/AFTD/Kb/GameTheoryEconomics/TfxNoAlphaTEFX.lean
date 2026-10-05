import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TfxAlphaTEFX
import AFTD.Kb.GameTheoryEconomics.TfxVal
import AFTD.Kb.GameTheoryEconomics.TfxCore

/-!
# tfx_no_alphaTEFX

Topic: fair_division   Node: cd5a408e039c

For the explicit instance with values 0, 1, x and three identical rounds, no allocation is α-TEFX whenever α x > 2, 2αx > x + 2 and α(x + 2) > x.
-/

/-- For the explicit instance with values `0, 1, x` and three identical rounds, no allocation is `α`-TEFX whenever `α x > 2`, `2αx > x + 2` and `α(x + 2) > x`. -/
theorem tfx_no_alphaTEFX (α x : ℝ) (hα0 : 0 < α) (hx0 : 0 < x) (h1 : 2 < α * x)
    (h2 : 2 + x < 2 * (α * x)) (h3 : x < 2 * α + α * x) (σ : Fin 3 → Fin 3 → Fin 2) :
    ¬ tfx_alphaTEFX α (tfx_val x) σ := by
  intro h
  have hσ : σ = ![![σ 0 0, σ 0 1, σ 0 2], ![σ 1 0, σ 1 1, σ 1 2], ![σ 2 0, σ 2 1, σ 2 2]] := by
    funext s g
    fin_cases s <;> fin_cases g <;> rfl
  rw [hσ] at h
  exact tfx_core α x hα0 hx0 h1 h2 h3 _ _ _ _ _ _ _ _ _ h
