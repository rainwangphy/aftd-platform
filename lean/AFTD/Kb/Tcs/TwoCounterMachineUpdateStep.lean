import AFTD.Prelude
import AFTD.Kb.Tcs.TwoCounterInstr
import AFTD.Kb.Tcs.TwoCounterMachine

/-!
# two_counter_machine_update_step

Topic: automata   Node: 8039996c3b7a

Provenance: helper lemma. step towards symmetric_two_counter_boundary_reachability_semilinear

The zero-test-free (update-only) one-step relation of a 2-counter machine M: an update transition from c₁.1 to c₂.1 with integer displacement (w₁, w₂) that is realised on the counters.
-/

/-- The update (2-VASS) part of the one-step relation: the counters move by (w₁, w₂) and neither counter is inspected. -/
def two_counter_machine_update_step {Q : Type*} (M : TwoCounterMachine Q) (c₁ c₂ : Q × ℕ × ℕ) : Prop :=
  ∃ w₁ w₂ : ℤ,
    (c₁.1, TwoCounterInstr.update w₁ w₂, c₂.1) ∈ M.transitions ∧
    (c₁.2.1 : ℤ) + w₁ = c₂.2.1 ∧ (c₁.2.2 : ℤ) + w₂ = c₂.2.2
