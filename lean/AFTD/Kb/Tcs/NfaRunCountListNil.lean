import AFTD.Prelude
import AFTD.Kb.Tcs.NfaRunCountList

/-!
# nfa_run_count_list_nil

Topic: automata   Node: 9c4b81049dbd

Provenance: helper lemma. step towards pell_nfa_run_count_lower_bound

There is exactly one empty run from p to q if p = q and none otherwise.
-/

open Classical in
/-- There is exactly one run of the empty word from p to q, namely when p = q. -/
theorem nfa_run_count_list_nil {α σ : Type*} [Fintype σ] (M : NFA α σ) (p q : σ) :
    nfa_run_count_list M [] p q = if p = q then 1 else 0 := by
  unfold nfa_run_count_list
  simp only [List.length_nil, Fin.last_zero, IsEmpty.forall_iff, and_true]
  split_ifs with h
  · subst h
    have : {r : Fin 1 → σ | r 0 = p ∧ r 0 = p} = {fun _ => p} := by
      ext r
      simp only [and_self, Set.mem_singleton_iff]
      constructor
      · intro hr
        ext i
        fin_cases i
        exact hr
      · rintro rfl
        rfl
    rw [this, Set.ncard_singleton]
  · have : {r : Fin 1 → σ | r 0 = p ∧ r 0 = q} = ∅ := by
      ext r
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨h1, h2⟩
      exact h (h1.symm.trans h2)
    rw [this, Set.ncard_empty]
