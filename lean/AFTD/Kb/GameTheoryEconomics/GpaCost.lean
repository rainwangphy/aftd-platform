import AFTD.Prelude

/-!
# gpa_cost

Topic: mechanism_design   Node: 072cc8973751

The convex signal cost of arXiv:2209.01146, Section 5.3: h(σ) = max{‖σ‖_∞ - 1/k, 0} (the norm on Fin k → ℝ is the sup norm).
-/

/-- The convex signal cost of arXiv:2209.01146, Section 5.3: `h(σ) = max{‖σ‖_∞ - 1/k, 0}` (the norm on `Fin k → ℝ` is the sup norm). -/
noncomputable def gpa_cost {k : ℕ} (σ : Fin k → ℝ) : ℝ :=
  max (‖σ‖ - 1 / (k : ℝ)) 0
