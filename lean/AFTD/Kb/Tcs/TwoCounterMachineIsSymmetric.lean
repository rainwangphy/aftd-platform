import AFTD.Prelude
import AFTD.Kb.Tcs.TwoCounterInstr
import AFTD.Kb.Tcs.TwoCounterMachine

/-!
# two_counter_machine_is_symmetric

Topic: automata   Node: 6876909461ff

Provenance: formalization of a published result. Source: arXiv:2610.23495, Sec. 2

A 2-counter machine M with state type Q is symmetric if for every update transition from q to q' with integer weights (w₁, w₂), the machine also contains the update transition from q to q' with swapped weights (w₂, w₁).
-/

/-- Predicate asserting that a 2-counter machine is symmetric under swapping the two counters. -/
def two_counter_machine_is_symmetric {Q : Type*} (M : TwoCounterMachine Q) : Prop :=
  ∀ q q' : Q, ∀ w₁ w₂ : ℤ,
    (q, TwoCounterInstr.update w₁ w₂, q') ∈ M.transitions →
    (q, TwoCounterInstr.update w₂ w₁, q') ∈ M.transitions
