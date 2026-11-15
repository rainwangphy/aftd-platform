import AFTD.Prelude
import AFTD.Kb.Tcs.DfaIsSynchronizing

/-!
# dfa_is_simultaneously_synchronizing

Topic: automata   Node: a2c474617f91

Provenance: formalization of a published result. Source: arXiv:2611.09136

Given an alphabet type α, a natural number k, a family of state types σ : Fin k → Type*, and a family of deterministic finite automata A : (i : Fin k) → DFA α (σ i), a word w : List α is simultaneously synchronizing for A if for every index i : Fin k, w is synchronizing for automaton A i.
-/

/-- A word synchronizes a family of deterministic finite automata with heterogeneous state spaces if it synchronizes each automaton in the family. -/
def dfa_is_simultaneously_synchronizing {α : Type*} {k : ℕ} {σ : Fin k → Type*}
    (A : (i : Fin k) → DFA α (σ i)) (w : List α) : Prop := ∀ i : Fin k, dfa_is_synchronizing (A i) w
