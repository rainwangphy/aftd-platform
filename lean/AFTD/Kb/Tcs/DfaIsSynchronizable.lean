import AFTD.Prelude
import AFTD.Kb.Tcs.DfaIsSynchronizing

/-!
# dfa_is_synchronizable

Topic: automata   Node: 142b96048146

Provenance: formalization of a published result. Source: arXiv:2611.09136 Sec. 2

A deterministic finite automaton `A : DFA α σ` is synchronizable if there exists a synchronizing word `w : List α` for `A`.
-/

/-- A DFA is synchronizable if it admits a synchronizing word. -/
def dfa_is_synchronizable {α σ : Type*} (A : DFA α σ) : Prop := ∃ w : List α, dfa_is_synchronizing A w
