import AFTD.Prelude
import AFTD.Kb.Tcs.PowerDivergenceGenerator

/-!
# power_divergence_generator_one

Topic: information   Node: 4c638592e058

Provenance: helper lemma. Sanity lemma for the power-divergence generator, arXiv:2610.21231 (On the subadditivity of mutual f-information), Sec. I.

f_β(1) = 0.
-/

theorem power_divergence_generator_one (β : ℝ) : power_divergence_generator β 1 = 0 := by
  simp [power_divergence_generator]
