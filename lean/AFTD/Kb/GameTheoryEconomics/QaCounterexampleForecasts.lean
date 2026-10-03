import AFTD.Prelude

/-!
# qa_counterexample_forecasts

Topic: mechanism_design   Node: 6b4f7c1e253d

The two expert forecasts (0, 0, 1) and (1/4, 3/4, 0) on three outcomes.
-/

/-- Experts `(0,0,1)` and `(1/4,3/4,0)` -/
noncomputable def qa_counterexample_forecasts : Fin 2 → Fin 3 → ℝ := ![![0, 0, 1], ![1/4, 3/4, 0]]
