import AFTD.Prelude
import AFTD.Kb.Tcs.CactusCycleEnvelope

/-!
# cactus_cycle_envelope_one

Topic: algorithms   Node: 1c420ab17aa6

Provenance: helper lemma. arXiv:2610.23032

The cactus cycle envelope cactus_cycle_envelope evaluated at 1 is equal to 1.
-/

/-- The cactus cycle envelope at m = 1 equals 1. -/
theorem cactus_cycle_envelope_one : cactus_cycle_envelope 1 = 1 := by
  unfold cactus_cycle_envelope
  norm_num
