import AFTD.Prelude
import AFTD.Kb.Tcs.TwoCounterMachineIsSingleCounterUpdate
import AFTD.Kb.Tcs.TwoCounterMachineStep
import AFTD.Kb.Tcs.TwoCounterMachine
import AFTD.Kb.Tcs.IsSingleCounterUpdate
import AFTD.Kb.Tcs.TwoCounterInstr

/-!
# single_counter_step_preserves_one_coord

Topic: automata   Node: 2c021d25d3a0

Provenance: helper lemma. step towards op_360_single_counter_update_strictly_less_expressive

In any single step of a 2-counter machine with single-counter updates, at least one counter remains unchanged.
-/

/-- In any single step of a 2-counter machine with single-counter updates, at least one counter remains unchanged. -/
theorem single_counter_step_preserves_one_coord {Q : Type*} (M : TwoCounterMachine Q)
    (hsc : two_counter_machine_is_single_counter_update M)
    (c₁ c₂ : Q × ℕ × ℕ) (hstep : two_counter_machine_step M c₁ c₂) :
    c₂.2.1 = c₁.2.1 ∨ c₂.2.2 = c₁.2.2 := by
  rcases hstep with (⟨w₁, w₂, htr, h₁, h₂⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩)
  · have hsc' := hsc c₁.1 c₂.1 w₁ w₂ htr
    rcases hsc' with hw₁ | hw₂
    · left
      subst hw₁
      simp only [add_zero] at h₁
      exact Nat.cast_injective h₁.symm
    · right
      subst hw₂
      simp only [add_zero] at h₂
      exact Nat.cast_injective h₂.symm
  · left
    exact congr_arg Prod.fst h
  · left
    exact congr_arg Prod.fst h
