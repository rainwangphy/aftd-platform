import AFTD.Prelude

/-!
# pcx_theta

Topic: equilibria   Node: 778d32a6a664

Types of the binary instance: theta = (1, 8).
-/

/-- The two-type, two-venue instance: type 0 (low, `θ = 1`, density 1/3) and type 1 (high, `θ = 8`, density 2/3). -/
noncomputable def pcx_theta : Fin 2 → ℝ := ![1, 8]
