import AFTD.Prelude
import AFTD.Kb.Tcs.NfaHasSingletonSccs
import AFTD.Kb.Tcs.PellNfa
import AFTD.Kb.Tcs.PellNfaStepTable

/-!
# pell_nfa_has_singleton_sccs

Topic: automata   Node: a56e441496e3

Provenance: helper lemma. arXiv:2610.08525 Appendix A

For every natural number n, the n-state Pell NFA pell_nfa n has singleton strongly connected components.
-/

lemma pell_nfa_has_singleton_sccs_evalFrom_le (n : ℕ) (w : List (Fin 5)) {p q : Fin n}
    (h : q ∈ (pell_nfa n).evalFrom {p} w) : p.val ≤ q.val := by
  induction w generalizing p with
  | nil =>
    simp only [NFA.evalFrom_nil, Set.mem_singleton_iff] at h
    subst h
    rfl
  | cons a w' ih =>
    simp only [NFA.evalFrom_cons, NFA.stepSet_singleton] at h
    rw [NFA.mem_evalFrom_iff_exists] at h
    rcases h with ⟨r, hr, hq⟩
    have h1 : p.val ≤ r.val := by
      have htab := pell_nfa_step_table n hr
      rcases htab with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
      · rcases h with h | h <;> omega
      · rcases h with h | h <;> omega
      · rcases h with h | h <;> omega
    have h2 : r.val ≤ q.val := ih hq
    omega

/-- The Pell NFA has singleton strongly connected components. -/
theorem pell_nfa_has_singleton_sccs (n : ℕ) : nfa_has_singleton_sccs (pell_nfa n) := by
  intro p q ⟨w1, hw1⟩ ⟨w2, hw2⟩
  have h1 := pell_nfa_has_singleton_sccs_evalFrom_le n w1 hw1
  have h2 := pell_nfa_has_singleton_sccs_evalFrom_le n w2 hw2
  ext
  omega
