import AFTD.Prelude

/-!
# pcx_cost

Topic: equilibria   Node: 861ae3012719

Costs of the binary instance: venue 0 costs 1 for both types; venue 1 costs 128 for the low type and 8 for the high type.
-/

/-- Publication costs of the instance: venue 0 costs 1 for both types; venue 1 costs 128 for the low type and 8 for the high type. -/
noncomputable def pcx_cost : Fin 2 → Fin 2 → ℝ := ![![1, 128], ![1, 8]]
