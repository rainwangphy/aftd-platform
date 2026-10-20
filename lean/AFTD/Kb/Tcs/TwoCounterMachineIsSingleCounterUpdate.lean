import AFTD.Prelude
import AFTD.Kb.Tcs.IsSingleCounterUpdate
import AFTD.Kb.Tcs.TwoCounterMachine
import AFTD.Kb.Tcs.TwoCounterInstr

/-!
# two_counter_machine_is_single_counter_update

Topic: automata   Node: 3143b9537410

Provenance: formalization of a published result. Source: scout/2610-23495-symmetric-two-counter-machines.md:1692

A 2-counter machine M with state type Q has single-counter updates if for every update transition from q to q' with displacements (w₁, w₂), the displacement vector satisfies IsSingleCounterUpdate w₁ w₂.
-/

/-- A 2-counter machine is single-counter update if every update transition modifies at most one counter. -/
def two_counter_machine_is_single_counter_update {Q : Type*} (M : TwoCounterMachine Q) : Prop := ∀ q q' : Q, ∀ w₁ w₂ : ℤ,
    (q, TwoCounterInstr.update w₁ w₂, q') ∈ M.transitions →
    IsSingleCounterUpdate w₁ w₂
