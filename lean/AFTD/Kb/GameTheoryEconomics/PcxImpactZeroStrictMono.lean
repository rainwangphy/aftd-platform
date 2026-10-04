import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PcxImpact

/-!
# pcx_impact_zero_strictMono

Topic: equilibria   Node: 4619021c7af8

The impact (1+16x)/(1+2x) of venue 0 is strictly increasing in x >= 0.
-/

/-- The impact of venue 0, `(1+16x)/(1+2x)`, is strictly increasing in `x ≥ 0`. -/
lemma pcx_impact_zero_strictMono {x y : ℝ} (hx : 0 ≤ x) (hxy : x < y) :
    pcx_impact x 0 < pcx_impact y 0 := by
  simp only [pcx_impact, Matrix.cons_val_zero]
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith
