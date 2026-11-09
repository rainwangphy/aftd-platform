import AFTD.Prelude
import AFTD.Kb.Tcs.DfaIsSynchronizing

/-!
# dfa_reset_threshold

Topic: automata   Node: 68a397d4fcca

Provenance: formalization of a published result. Source: arXiv:2611.09136 Section 2

The reset threshold `dfa_reset_threshold A` of a deterministic finite automaton `A : DFA α σ` is the infimum in `WithTop ℕ` of the lengths of all synchronizing words for `A`.
-/

/-- The reset threshold of a DFA is the infimum in WithTop ℕ of the lengths of all synchronizing words. -/
noncomputable def dfa_reset_threshold {α σ : Type*} (A : DFA α σ) : WithTop ℕ := sInf ((fun w : List α => (w.length : WithTop ℕ)) '' { w | dfa_is_synchronizing A w })
