import AFTD.Prelude
import AFTD.Kb.Tcs.TwoCounterMachineIsSymmetric
import AFTD.Kb.Tcs.TwoCounterMachineIsSingleCounterUpdate
import AFTD.Kb.Tcs.TwoCounterMachineReachRel
import AFTD.Kb.Tcs.SingleCounterStepPreservesOneCoord
import AFTD.Kb.Tcs.DiagTwoCounterMachineIsSymmetric
import AFTD.Kb.Tcs.DiagTwoCounterMachineReachRelIff
import AFTD.Kb.Tcs.SingleCounterSymmetricCannotMatchDiagReach
import AFTD.Kb.Tcs.TwoCounterInstr
import AFTD.Kb.Tcs.TwoCounterMachine

/-!
# op_360_single_counter_update_strictly_less_expressive

Topic: automata   Node: 2a5789fb008f

Provenance: formalization of a published result. Source: scout/2610-23495-symmetric-two-counter-machines.md:304

There exists a symmetric 2-counter machine M over a finite state type Q and states q, q' in Q whose reachability relation two_counter_machine_reach_rel M q q' cannot be realized as the reachability relation two_counter_machine_reach_rel M' q0 q1 between any states q0, q1 of any finite-state symmetric 2-counter machine M' with single-counter updates.
-/

/-- Open Problem OP-360: The single-counter update fragment of symmetric 2-counter machines is strictly less expressive in terms of reachability relations than unrestricted symmetric 2-counter machines. -/
theorem op_360_single_counter_update_strictly_less_expressive :
    ∃ (Q : Type) (_ : Finite Q) (M : TwoCounterMachine Q) (_ : two_counter_machine_is_symmetric M) (q q' : Q),
      ∀ (Q' : Type) (_ : Finite Q') (M' : TwoCounterMachine Q') (_ : two_counter_machine_is_symmetric M')
        (_ : two_counter_machine_is_single_counter_update M') (q0 q1 : Q'),
        two_counter_machine_reach_rel M' q0 q1 ≠ two_counter_machine_reach_rel M q q' := by
  refine ⟨Bool, inferInstance, ⟨{(false, TwoCounterInstr.update 1 1, true)}⟩,
    diag_two_counter_machine_is_symmetric, false, true, ?_⟩
  intro Q' hQ' M' hsymm hsc q0 q1
  exact single_counter_symmetric_cannot_match_diag_reach Q' hQ' M' hsymm hsc q0 q1
