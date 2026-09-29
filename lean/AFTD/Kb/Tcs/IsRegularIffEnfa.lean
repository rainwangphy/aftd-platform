import AFTD.Prelude
import AFTD.Kb.Tcs.IsRegularIffNfa

/-!
# is_regular_iff_enfa

Topic: automata   Node: fa4057073cb1

A language is regular if and only if it is accepted by an epsilon-nondeterministic finite automaton with finitely many states.
-/

/-- A language is regular if and only if it is accepted by an epsilon-nondeterministic finite automaton with finitely many states. -/
theorem is_regular_iff_enfa {α : Type*} {L : Language α} : L.IsRegular ↔ ∃ (σ : Type) (_ : Fintype σ) (M : εNFA α σ), M.accepts = L := by
  rw [is_regular_iff_nfa]
  constructor
  · rintro ⟨σ, _, M, rfl⟩
    exact ⟨σ, inferInstance, M.toεNFA, M.toεNFA_correct⟩
  · rintro ⟨σ, _, M, rfl⟩
    exact ⟨σ, inferInstance, M.toNFA, M.toNFA_correct⟩
