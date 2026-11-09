import AFTD.Prelude
import AFTD.Kb.Tcs.DfaIsSynchronizable
import AFTD.Kb.Tcs.DfaIsSynchronizingSubsingleton
import AFTD.Kb.Tcs.DfaIsSynchronizing

/-!
# dfa_is_synchronizable_subsingleton

Topic: automata   Node: 9ca5a0490c46

Provenance: helper lemma. folklore

Every deterministic finite automaton whose state type is a subsingleton is synchronizable.
-/

/-- Sanity lemma: a DFA on a subsingleton state type is synchronizable. -/
theorem dfa_is_synchronizable_subsingleton {α σ : Type*} [Subsingleton σ] (A : DFA α σ) : dfa_is_synchronizable A := ⟨[], dfa_is_synchronizing_subsingleton A []⟩
