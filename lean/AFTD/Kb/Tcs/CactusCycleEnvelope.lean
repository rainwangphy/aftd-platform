import AFTD.Prelude

/-!
# cactus_cycle_envelope

Topic: algorithms   Node: 5d5db15d1f13

Provenance: original. Related work: arXiv:2610.23032

For a natural number m, the cactus cycle envelope cactus_cycle_envelope m is defined as the real number (3 * (2 : ℝ) ^ (m - 1) - 2) / ((2 : ℝ) ^ m - 1).
-/

/-- The exact cycle envelope function (3 * 2^(m - 1) - 2) / (2^m - 1) for endpoint-cut-stable trees on cactus metrics. -/
noncomputable def cactus_cycle_envelope (m : ℕ) : ℝ := (3 * (2 : ℝ) ^ (m - 1) - 2) / ((2 : ℝ) ^ m - 1)
