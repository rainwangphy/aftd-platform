import AFTD.Prelude
import AFTD.Kb.Tcs.TwoCounterMachineZeroTestStep
import AFTD.Kb.Tcs.TwoCounterMachine

/-!
# two_counter_machine_zero_test_state_reach

Topic: automata   Node: 6f8d8177b287

Provenance: helper lemma. step towards symmetric_two_counter_boundary_reachability_semilinear

q' is reachable from q by a sequence of zero tests while the counter vector is held fixed at p.
-/

/-- Zero-test reachability at a frozen counter vector p: the reflexive-transitive closure of the zero-test step relation restricted to the fibre over p. -/
def two_counter_machine_zero_test_state_reach {Q : Type*} (M : TwoCounterMachine Q) (p : ℕ × ℕ) (q q' : Q) : Prop :=
  Relation.ReflTransGen (fun a b : Q => two_counter_machine_zero_test_step M (a, p) (b, p)) q q'
