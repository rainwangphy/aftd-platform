import AFTD.Prelude
import AFTD.Kb.Tcs.BinaryExtremizerNfa
import AFTD.Kb.Tcs.NfaHasSingletonSccs

/-!
# binary_extremizer_has_singleton_sccs

Topic: automata   Node: 775f62eeb56c

Provenance: helper lemma. arXiv:2610.08525, Stronger bounds on the degree of ambiguity of finite automata

For every natural number n, the binary extremizer NFA binary_extremizer_nfa n has singleton strongly connected components.
-/

lemma binary_extremizer_has_singleton_sccs_step_le {n : ℕ} {p q : Fin n} {k : Fin 2}
    (h : q ∈ (binary_extremizer_nfa n).step p k) : p.val ≤ q.val := by
  dsimp [binary_extremizer_nfa] at h
  rcases h with hlt | ⟨-, hp, hq⟩ | ⟨-, -, hqp⟩
  · exact le_of_lt hlt
  · rw [hp, hq]
  · rw [hqp]

lemma binary_extremizer_has_singleton_sccs_evalFrom_le (n : ℕ) (w : List (Fin 2)) {p q : Fin n}
    (h : q ∈ (binary_extremizer_nfa n).evalFrom {p} w) : p.val ≤ q.val := by
  induction' w with a w ih generalizing p
  · simp only [NFA.evalFrom_nil, Set.mem_singleton_iff] at h
    rw [h]
  · rw [NFA.evalFrom_cons, NFA.stepSet_singleton] at h
    rw [NFA.mem_evalFrom_iff_exists] at h
    rcases h with ⟨r, hr, hq⟩
    have h1 := binary_extremizer_has_singleton_sccs_step_le hr
    have h2 := ih hq
    exact le_trans h1 h2

/-- The binary extremizer automaton has singleton strongly connected components. -/
theorem binary_extremizer_has_singleton_sccs (n : ℕ) :
    nfa_has_singleton_sccs (binary_extremizer_nfa n) := by
  intro p q ⟨w1, hw1⟩ ⟨w2, hw2⟩
  have h1 := binary_extremizer_has_singleton_sccs_evalFrom_le n w1 hw1
  have h2 := binary_extremizer_has_singleton_sccs_evalFrom_le n w2 hw2
  ext
  omega
