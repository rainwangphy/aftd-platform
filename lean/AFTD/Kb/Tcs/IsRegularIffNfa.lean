import AFTD.Prelude

/-!
# is_regular_iff_nfa

Topic: automata   Node: 0f00610d529b

A language is regular if and only if it is accepted by a nondeterministic finite automaton with finitely many states.
-/

/-- A language is regular if and only if it is accepted by a nondeterministic finite automaton with finitely many states. -/
theorem is_regular_iff_nfa {α : Type*} {L : Language α} : L.IsRegular ↔ ∃ (σ : Type) (_ : Fintype σ) (M : NFA α σ), M.accepts = L := by
  constructor
  · rintro ⟨σ, _, M, rfl⟩
    exact ⟨σ, inferInstance, M.toNFA, M.toNFA_correct⟩
  · rintro ⟨σ, _, M, rfl⟩
    exact ⟨Set σ, inferInstance, M.toDFA, NFA.toDFA_correct⟩
