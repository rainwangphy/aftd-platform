import AFTD.Prelude
import AFTD.Kb.Tcs.BitwordIsAperiodic
import AFTD.Kb.Tcs.BitwordRotate

/-!
# bitword_is_aperiodic_sanity

Topic: combinatorics   Node: f67b98b52053

Provenance: helper lemma. sanity check for bitword_is_aperiodic

Sanity check: the 6-bit word 001011 is aperiodic, while 001001 is fixed by rotation by 3.
-/

theorem bitword_is_aperiodic_sanity : bitword_is_aperiodic 6 11 ∧ ¬ bitword_is_aperiodic 6 9 := by
  refine ⟨?_, fun h => h 3 (by decide) (by decide) (by decide)⟩
  intro r h0 h6
  interval_cases r <;> decide
