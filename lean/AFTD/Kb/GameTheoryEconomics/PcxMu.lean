import AFTD.Prelude

/-!
# pcx_mu

Topic: equilibria   Node: 098cb3290e1c

Type densities of the binary instance: (1/3, 2/3).
-/

/-- Type densities of the instance: 1/3 low, 2/3 high. -/
noncomputable def pcx_mu : Fin 2 → ℝ := ![1 / 3, 2 / 3]
