import AFTD.Prelude
import AFTD.Kb.Tcs.TwoWayDfa
import AFTD.Kb.Tcs.TwoWayDfaStep

/-!
# two_way_dfa_run

Topic: automata   Node: 0ac95b8bf1b1

Provenance: formalization of a published result. Source: arXiv:2610.18897 (A factor-two lower bound for complementing two-way deterministic finite automata), Section 2.1: the computation from (s, 0)

The configuration after t steps of the computation from (s, 0) on w, or none once it has halted on an undefined transition.
-/

def two_way_dfa_run {σ Q : Type*} (A : two_way_dfa σ Q) (w : List σ) (t : ℕ) : Option (Q × ℕ) :=
  (fun c => c.bind (two_way_dfa_step A w))^[t] (some (A.s, 0))
