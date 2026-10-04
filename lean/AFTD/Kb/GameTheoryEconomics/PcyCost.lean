import AFTD.Prelude

/-!
# pcy_cost

Topic: equilibria   Node: e4d80179491f

Costs of the three-type instance: venue 0 costs 1 for every type; venue 1 costs 128, 64 and 8.
-/

/-- Publication costs of the three-type instance: venue 0 costs 1 for every type; venue 1 costs 128, 64 and 8 for the three types. -/
noncomputable def pcy_cost : Fin 3 → Fin 2 → ℝ := ![![1, 128], ![1, 64], ![1, 8]]
