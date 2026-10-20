import AFTD.Prelude
import AFTD.Kb.Tcs.TwoCounterInstr
import AFTD.Kb.Tcs.TwoCounterMachine

/-!
# two_counter_machine_step

Topic: automata   Node: 42e42ca21ced

Provenance: formalization of a published result. Source: arXiv:2610.23495, Sec. 2

The one-step transition relation of a 2-counter machine M between configurations c₁ and c₂ in Q × (ℕ × ℕ): either an update transition from c₁.1 to c₂.1 with displacement (w₁, w₂) modifies the counters by (w₁, w₂), or a zero-test transition on counter 1 occurs when counter 1 is 0 and leaves counters unchanged, or a zero-test transition on counter 2 occurs when counter 2 is 0 and leaves counters unchanged.
-/

/-- One-step transition relation between configurations of a 2-counter machine. -/
def two_counter_machine_step {Q : Type*} (M : TwoCounterMachine Q) (c₁ c₂ : Q × (ℕ × ℕ)) : Prop :=
  (∃ w₁ w₂ : ℤ,
    (c₁.1, TwoCounterInstr.update w₁ w₂, c₂.1) ∈ M.transitions ∧
    (c₁.2.1 : ℤ) + w₁ = c₂.2.1 ∧ (c₁.2.2 : ℤ) + w₂ = c₂.2.2) ∨
  ((c₁.1, TwoCounterInstr.zeroTest₁, c₂.1) ∈ M.transitions ∧
    c₁.2.1 = 0 ∧ c₂.2 = c₁.2) ∨
  ((c₁.1, TwoCounterInstr.zeroTest₂, c₂.1) ∈ M.transitions ∧
    c₁.2.2 = 0 ∧ c₂.2 = c₁.2)
