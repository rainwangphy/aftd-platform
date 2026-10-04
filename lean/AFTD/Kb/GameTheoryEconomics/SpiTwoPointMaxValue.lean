import AFTD.Prelude

/-!
# spi_two_point_max_value

Topic: mechanism_design   Node: d23bd348086a

The searcher's expected reward from a two-point player using an optimal scheme (E[X] if T <= E[X], T times the pooling probability if E[X] < T <= h, 0 above h).
-/

/-- The searcher's expected reward from a two-point player using an optimal scheme (no information if `T ≤ E[X]`, pooling the top mass to posterior mean exactly `T` otherwise). -/
noncomputable def spi_two_point_max_value (h l q T : ℝ) : ℝ :=
  if T ≤ q * h + (1 - q) * l then q * h + (1 - q) * l else if T ≤ h then T * (q * (h - l) / (T - l)) else 0
