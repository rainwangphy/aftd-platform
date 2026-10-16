import AFTD.Prelude

/-!
# power_divergence_generator

Topic: information   Node: ece002f146ff

Provenance: formalization of a published result. Source: arXiv:2610.21231 (On the subadditivity of mutual f-information), Sec. I (power divergences f_β).

The power-divergence generator f_β(x) = (x^β − βx + β − 1)/(β(β − 1)), for β ∉ {0, 1} and x ≥ 0 (β = 1/2 gives 2(√x − 1)², the squared Hellinger generator).
-/

/-- The power-divergence generator `f_β(x) = (x^β − β x + (β − 1)) / (β (β − 1))` (real power `x ^ β`). -/
noncomputable def power_divergence_generator (β x : ℝ) : ℝ :=
  (x ^ β - β * x + (β - 1)) / (β * (β - 1))
