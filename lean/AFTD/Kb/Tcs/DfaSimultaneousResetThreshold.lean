import AFTD.Prelude
import AFTD.Kb.Tcs.DfaIsSynchronizing

/-!
# dfa_simultaneous_reset_threshold

Topic: automata   Node: 53c3ec04f3cc

Provenance: formalization of a published result. Source: arXiv:2611.09136

Given an alphabet type α, a natural number k, a family of state types σ : Fin k → Type*, and a family of deterministic finite automata A : (i : Fin k) → DFA α (σ i), the simultaneous reset threshold of A is the infimum in WithTop ℕ of the lengths of all words w : List α that simultaneously synchronize every automaton A i in the family (evaluating to ⊤ if no such word exists).
-/

/-- The simultaneous reset threshold of a family of deterministic finite automata with heterogeneous state spaces is the infimum in WithTop ℕ of the lengths of simultaneously synchronizing words. -/
noncomputable def dfa_simultaneous_reset_threshold {α : Type*} {k : ℕ} {σ : Fin k → Type*}
    (A : (i : Fin k) → DFA α (σ i)) : WithTop ℕ := sInf ((fun w : List α => (w.length : WithTop ℕ)) '' { w | ∀ i : Fin k, dfa_is_synchronizing (A i) w })
