import AFTD.Prelude
import AFTD.Kb.Tcs.Op75Tm2DoublePushMachine

/-!
# op75_tm2_two_push_one_step

Topic: np_completeness   Node: 97967638d20e

Provenance: helper lemma. OP-75 Karp-reduction composition: finite-statement stack-growth bound in the repository TM2 model.

The explicit machine outputs two true symbols from an empty input in one TM2 step.
-/

theorem op75_tm2_two_push_one_step :
    Nonempty (Turing.TM2OutputsInTime op75_tm2_double_push_machine [] (some [true,true]) 1) := by
  refine ⟨{ steps := 1, evals_in_steps := ?_, steps_le_m := by omega }⟩
  rfl
