import AFTD.Prelude

/-!
# fse_cost

Topic: mechanism_design   Node: c6d91df3977c

Facility location with scaling effects (arXiv 2402.18908): an agent located at x incurs cost q y * |x - y| when the facility is placed at y, where q is the (public) scaling function.
-/

/-- Facility location with scaling effects (arXiv 2402.18908): an agent located at `x` incurs cost `q y * |x - y|` when the facility is placed at `y`, where `q` is the (public) scaling function. -/
noncomputable def fse_cost (q : ℝ → ℝ) (y x : ℝ) : ℝ := q y * |x - y|
