import AFTD.Prelude
import AFTD.Kb.Tcs.TwoCounterMachineStep
import AFTD.Kb.Tcs.TwoCounterMachine

/-!
# two_counter_machine_reach_rel

Topic: automata   Node: 50ee0a0d2b54

Provenance: formalization of a published result. Source: arXiv:2610.23495, Sec. 1 and Sec. 3

For a 2-counter machine M with state type Q and states q, q' in Q, the reachability relation two_counter_machine_reach_rel M q q' is the set of pairs of counter vectors (u, v) in (ℕ × ℕ) × (ℕ × ℕ) such that configuration (q', v) is reachable from configuration (q, u) under the reflexive-transitive closure of the step relation of M.
-/

/-- The reachability relation between pairs of counter vectors for fixed control states in a 2-counter machine. -/
def two_counter_machine_reach_rel {Q : Type*} (M : TwoCounterMachine Q) (q q' : Q) : Set ((ℕ × ℕ) × (ℕ × ℕ)) :=
  { p | Relation.ReflTransGen (two_counter_machine_step M) (q, p.1) (q', p.2) }
