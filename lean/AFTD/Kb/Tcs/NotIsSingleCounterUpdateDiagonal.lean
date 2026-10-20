import AFTD.Prelude
import AFTD.Kb.Tcs.IsSingleCounterUpdate

/-!
# not_is_single_counter_update_diagonal

Topic: automata   Node: 3a29beb816ab

Provenance: helper lemma. scout/2610-23495-symmetric-two-counter-machines.md:1692

The simultaneous increment (1, 1) is not a single-counter update.
-/

/-- The diagonal update (1, 1) is not a single-counter update. -/
lemma not_is_single_counter_update_diagonal : ¬ IsSingleCounterUpdate 1 1 := by
  simp [IsSingleCounterUpdate]
