import AFTD.Prelude
import AFTD.Kb.Tcs.TwoCounterInstr
import AFTD.Kb.Tcs.TwoCounterMachine

/-!
# two_counter_machine_zero_test_step

Topic: automata   Node: 7aa79e2daf39

Provenance: helper lemma. step towards symmetric_two_counter_boundary_reachability_semilinear

The zero-test one-step relation of a 2-counter machine M: a zero test on counter i is taken (which requires counter i to be 0) and the counter vector is left unchanged.
-/

/-- The zero-test part of the one-step relation: only the control state can change, both counters are preserved. -/
def two_counter_machine_zero_test_step {Q : Type*} (M : TwoCounterMachine Q) (c₁ c₂ : Q × ℕ × ℕ) : Prop :=
  ((c₁.1, TwoCounterInstr.zeroTest₁, c₂.1) ∈ M.transitions ∧ c₁.2.1 = 0 ∧ c₂.2 = c₁.2) ∨
  ((c₁.1, TwoCounterInstr.zeroTest₂, c₂.1) ∈ M.transitions ∧ c₁.2.2 = 0 ∧ c₂.2 = c₁.2)
