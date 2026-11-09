import AFTD.Prelude

/-!
# dfa_is_synchronizing

Topic: automata   Node: c494cf3b9c34

Provenance: formalization of a published result. Source: arXiv:2611.09136 Section 2

A word `w : List α` is synchronizing for a deterministic finite automaton `A : DFA α σ` if `A.evalFrom q₁ w = A.evalFrom q₂ w` for all states `q₁ q₂ : σ`.
-/

/-- A word w is synchronizing for a DFA A if it maps all states to the same state. -/
def dfa_is_synchronizing {α σ : Type*} (A : DFA α σ) (w : List α) : Prop := ∀ q₁ q₂ : σ, A.evalFrom q₁ w = A.evalFrom q₂ w
