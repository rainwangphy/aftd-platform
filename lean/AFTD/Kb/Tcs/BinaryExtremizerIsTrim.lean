import AFTD.Prelude
import AFTD.Kb.Tcs.BinaryExtremizerNfa
import AFTD.Kb.Tcs.NfaIsTrim

/-!
# binary_extremizer_is_trim

Topic: automata   Node: d4f82643c6fc

Provenance: helper lemma. arXiv:2610.08525, Stronger bounds on the degree of ambiguity of finite automata

For every positive natural number n, the binary extremizer NFA binary_extremizer_nfa n is trim: every state is reachable from the start state and can reach the accepting state.
-/

/-- The binary extremizer automaton is trim for every n ≥ 1. -/
theorem binary_extremizer_is_trim (n : ℕ) (hn : 1 ≤ n) :
    nfa_is_trim (binary_extremizer_nfa n) := by
  intro q
  constructor
  · by_cases hq : (q : ℕ) = 0
    · use []
      simp only [NFA.evalFrom_nil]
      change (q : ℕ) = 0
      exact hq
    · use [0]
      simp only [NFA.evalFrom_singleton, NFA.stepSet, Set.mem_iUnion]
      refine ⟨⟨0, hn⟩, ?_, ?_⟩
      · change (⟨0, hn⟩ : Fin n).1 = 0
        rfl
      · change (⟨0, hn⟩ : Fin n).1 < (q : ℕ) ∨ _
        dsimp
        left
        omega
  · by_cases hq : (q : ℕ) + 1 = n
    · use []
      refine ⟨q, ?_, ?_⟩
      · change (q : ℕ) + 1 = n
        exact hq
      · simp only [NFA.evalFrom_nil, Set.mem_singleton]
    · use [0]
      have htn : n - 1 < n := by omega
      refine ⟨⟨n - 1, htn⟩, ?_, ?_⟩
      · change (⟨n - 1, htn⟩ : Fin n).1 + 1 = n
        dsimp
        omega
      · simp only [NFA.evalFrom_singleton, NFA.stepSet, Set.mem_iUnion]
        refine ⟨q, by simp, ?_⟩
        change (q : ℕ) < (⟨n - 1, htn⟩ : Fin n).1 ∨ _
        dsimp
        left
        have : (q : ℕ) < n := q.is_lt
        omega
