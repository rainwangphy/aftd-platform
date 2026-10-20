import AFTD.Prelude
import AFTD.Kb.Tcs.TwoCounterMachineIsSymmetric
import AFTD.Kb.Tcs.TwoCounterMachine
import AFTD.Kb.Tcs.TwoCounterInstr

/-!
# diag_two_counter_machine_is_symmetric

Topic: automata   Node: 8d584ffb1dde

Provenance: helper lemma. step towards op_360_single_counter_update_strictly_less_expressive

The 2-counter machine over Bool with a single update (1, 1) from false to true is symmetric.
-/

/-- The 2-counter machine over Bool with a single update (1, 1) from false to true is symmetric. -/
theorem diag_two_counter_machine_is_symmetric :
    two_counter_machine_is_symmetric (⟨{(false, TwoCounterInstr.update 1 1, true)}⟩ : TwoCounterMachine Bool) := by
  intro q q' w₁ w₂ h
  simp only [Finset.mem_singleton, Prod.mk.injEq, TwoCounterInstr.update.injEq] at h ⊢
  tauto
