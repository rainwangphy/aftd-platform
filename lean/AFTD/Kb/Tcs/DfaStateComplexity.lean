import AFTD.Prelude

/-!
# dfa_state_complexity

Topic: automata   Node: 410f0bdf330b

Provenance: original. Related work: folklore

The deterministic state complexity of a language L is the minimum number of states in any deterministic finite automaton (DFA) with finite state set in Type that recognizes L.
-/

/-- The deterministic state complexity of a language is the minimum number of states in a DFA accepting it. -/
noncomputable def dfa_state_complexity {α : Type*} (L : Language α) : ℕ := sInf { k : ℕ | ∃ (σ : Type) (_ : Fintype σ) (M : DFA α σ), Fintype.card σ = k ∧ M.accepts = L }
