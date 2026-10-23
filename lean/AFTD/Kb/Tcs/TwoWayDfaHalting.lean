import AFTD.Prelude
import AFTD.Kb.Tcs.TwoWayDfa
import AFTD.Kb.Tcs.TwoWayDfaRun

/-!
# two_way_dfa_halting

Topic: automata   Node: ff6d0dfa496c

Provenance: formalization of a published result. Source: arXiv:2610.18897 (A factor-two lower bound for complementing two-way deterministic finite automata), Section 7: a halting recognizer

A is halting: on every input its computation stops, by an undefined transition or by reaching the accepting configuration (f, 0).
-/

def two_way_dfa_halting {σ Q : Type*} (A : two_way_dfa σ Q) : Prop :=
  ∀ w, ∃ t, two_way_dfa_run A w t = none ∨ two_way_dfa_run A w t = some (A.f, 0)
