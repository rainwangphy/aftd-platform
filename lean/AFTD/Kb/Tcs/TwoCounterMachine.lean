import AFTD.Prelude
import AFTD.Kb.Tcs.TwoCounterInstr

/-!
# TwoCounterMachine

Topic: automata   Node: 621eb6f412ad

Provenance: formalization of a published result. Source: arXiv:2610.23495, Section 2

A structure TwoCounterMachine parameterized by a type of control states Q : Type*, consisting of a single field transitions which is a finite set of triples (q, instr, q') with q, q' ∈ Q and instr ∈ TwoCounterInstr.
-/

/-- A structure parameterized by a type of control states Q, consisting of a finite set of transitions labelled by 2-counter instructions. -/
structure TwoCounterMachine (Q : Type*) where transitions : Finset (Q × TwoCounterInstr × Q)
