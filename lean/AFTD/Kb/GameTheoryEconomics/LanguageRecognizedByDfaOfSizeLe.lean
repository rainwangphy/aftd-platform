import AFTD.Prelude

/-!
# language_recognized_by_dfa_of_size_le

Topic: combinatorial_games   Node: 419fc6e06925

Provenance: formalization of a published result. Source: arXiv:2611.09157 Problem 2.1

A language L is recognized by a deterministic finite automaton with at most k states.
-/

/-- Predicate that a language is recognized by a DFA with at most k states. -/
def language_recognized_by_dfa_of_size_le {α : Type*} (L : Language α) (k : ℕ) : Prop := ∃ (σ : Type) (_ : Fintype σ) (M : DFA α σ), Fintype.card σ ≤ k ∧ M.accepts = L
