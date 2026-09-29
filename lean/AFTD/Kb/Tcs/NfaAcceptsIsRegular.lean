import AFTD.Prelude

/-!
# nfa_accepts_is_regular

Topic: automata   Node: 0ae3a2ce014e

The language accepted by any finite-state nondeterministic finite automaton is regular.
-/

/-- The language accepted by any finite-state nondeterministic finite automaton is regular. -/
theorem nfa_accepts_is_regular {α : Type*} {σ : Type*} [Fintype σ] (M : NFA α σ) : M.accepts.IsRegular := Language.isRegular_iff.2 ⟨Set σ, inferInstance, M.toDFA, NFA.toDFA_correct⟩
