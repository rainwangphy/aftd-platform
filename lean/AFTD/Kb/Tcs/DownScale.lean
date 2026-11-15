import AFTD.Prelude

/-!
# down_scale

Topic: online_algorithms   Node: 2c24eccc8e68

Provenance: formalization of a published result. Source: arXiv:2611.17090, Section 3.1, Eq. (1)

Downward rounding down_θ(z) to the nearest scale in R_θ bounded by z: 0 if z ≤ 0, and 2^{θ + ⌊log₂ z - θ⌋} if z > 0.
-/

/-- Downward rounding of a positive real to the nearest shifted dyadic scale in R_θ. -/
noncomputable def down_scale (θ : ℝ) (z : ℝ) : ℝ := if z ≤ 0 then 0 else (2 : ℝ) ^ (θ + (⌊Real.logb 2 z - θ⌋ : ℝ))
