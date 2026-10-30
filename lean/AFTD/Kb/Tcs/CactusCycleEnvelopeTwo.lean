import AFTD.Prelude
import AFTD.Kb.Tcs.CactusCycleEnvelope

/-!
# cactus_cycle_envelope_two

Topic: algorithms   Node: b6e34d95c3b5

Provenance: helper lemma. arXiv:2610.23032

The cactus cycle envelope cactus_cycle_envelope evaluated at 2 is equal to 4 / 3.
-/

/-- The cactus cycle envelope at m = 2 equals 4 / 3. -/
theorem cactus_cycle_envelope_two : cactus_cycle_envelope 2 = 4 / 3 := by
  unfold cactus_cycle_envelope
  norm_num
