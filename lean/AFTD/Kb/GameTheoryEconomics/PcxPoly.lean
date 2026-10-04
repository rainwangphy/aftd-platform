import AFTD.Prelude

/-!
# pcx_poly

Topic: equilibria   Node: ff45adc5b667

The cleared characteristic polynomial of the binary instance in the ratio x of high- to low-type publications at venue 0.
-/

/-- The cleared characteristic polynomial of the instance: `x * D_high - D_low` multiplied by `(1+2x)^4 (1+512x)^4`, where the venue impacts are `(1+16x)/(1+2x)` and `(1+4096x)/(1+512x)`. -/
noncomputable def pcx_poly (x : ℝ) : ℝ :=
  x * ((1 + 16 * x) ^ 4 * (1 + 512 * x) ^ 4 + (1 + 4096 * x) ^ 4 * (1 + 2 * x) ^ 4 / 8) -
    ((1 + 16 * x) ^ 4 * (1 + 512 * x) ^ 4 + (1 + 4096 * x) ^ 4 * (1 + 2 * x) ^ 4 / 128)
