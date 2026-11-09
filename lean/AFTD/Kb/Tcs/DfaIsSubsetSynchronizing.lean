import AFTD.Prelude

/-!
# dfa_is_subset_synchronizing

Topic: automata   Node: 8181ff67b345

Provenance: formalization of a published result. Source: arXiv:2611.09136 Sec. 7

A word `w : List α` is subset-synchronizing for a subset `S : Set σ` of states of a deterministic finite automaton `A : DFA α σ` if `A.evalFrom q₁ w = A.evalFrom q₂ w` for all `q₁ q₂ ∈ S`.
-/

/-- A word synchronizes a subset of states in a DFA if it maps all states in the subset to a common state. -/
def dfa_is_subset_synchronizing {α σ : Type*} (A : DFA α σ) (S : Set σ) (w : List α) : Prop := ∀ q₁ ∈ S, ∀ q₂ ∈ S, A.evalFrom q₁ w = A.evalFrom q₂ w
