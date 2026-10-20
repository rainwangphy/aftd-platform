import AFTD.Prelude
import AFTD.Kb.Tcs.TwoCounterInstr
import AFTD.Kb.Tcs.TwoCounterMachine

/-!
# two_counter_machine_is_vass

Topic: automata   Node: 7d4356c8fd50

Provenance: formalization of a published result. Source: arXiv:2610.23495, Sec. 2

A 2-counter machine M is a vector addition system with states (2-VASS) if every transition in M.transitions is an update transition.
-/

/-- Predicate asserting that a 2-counter machine is a 2-VASS, having only update transitions. -/
def two_counter_machine_is_vass {Q : Type*} (M : TwoCounterMachine Q) : Prop :=
  ∀ t ∈ M.transitions, ∃ q w₁ w₂ q', t = (q, TwoCounterInstr.update w₁ w₂, q')
