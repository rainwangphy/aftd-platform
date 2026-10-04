import AFTD.Prelude

/-!
# pcx_impact

Topic: equilibria   Node: f06944f7ba52

Venue impacts of the binary instance as functions of x: ((1+16x)/(1+2x), (1+4096x)/(1+512x)).
-/

/-- Venue impacts of the instance as a function of the ratio `x` of high-type to low-type publications on venue 0. -/
noncomputable def pcx_impact (x : ℝ) : Fin 2 → ℝ :=
  ![(1 + 16 * x) / (1 + 2 * x), (1 + 4096 * x) / (1 + 512 * x)]
