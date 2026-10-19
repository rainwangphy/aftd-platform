import AFTD.Prelude
import AFTD.Kb.Tcs.NfaRunCountList
import AFTD.Kb.Tcs.PellWord
import AFTD.Kb.Tcs.PellNfa

/-!
# pell_run_encard_eq_count

Topic: automata   Node: 50e12c1b0081

Provenance: helper lemma. step towards pell_nfa_run_count_lower_bound

The set of accepting runs of u_n in A_n has encard equal to the number of runs from q_1 to q_n.
-/

open Classical in
/-- The set of accepting runs of u_n in A_n has the same cardinality as the run count from q_1 to q_n. -/
theorem pell_run_encard_eq_count (n : ℕ) (hn : 3 ≤ n) :
    Set.encard {r : Fin ((pell_word n).length + 1) → Fin n |
        r 0 ∈ (pell_nfa n).start ∧
        r (Fin.last (pell_word n).length) ∈ (pell_nfa n).accept ∧
        ∀ i : Fin (pell_word n).length,
          r i.succ ∈ (pell_nfa n).step (r i.castSucc) ((pell_word n).get i)}
      = (nfa_run_count_list (pell_nfa n) (pell_word n) ⟨0, by omega⟩ ⟨n - 1, by omega⟩ : ℕ∞) := by
  have hset : {r : Fin ((pell_word n).length + 1) → Fin n |
        r 0 ∈ (pell_nfa n).start ∧
        r (Fin.last (pell_word n).length) ∈ (pell_nfa n).accept ∧
        ∀ i : Fin (pell_word n).length,
          r i.succ ∈ (pell_nfa n).step (r i.castSucc) ((pell_word n).get i)}
      = {r : Fin ((pell_word n).length + 1) → Fin n |
        r 0 = ⟨0, by omega⟩ ∧
        r (Fin.last (pell_word n).length) = ⟨n - 1, by omega⟩ ∧
        ∀ i : Fin (pell_word n).length,
          r i.succ ∈ (pell_nfa n).step (r i.castSucc) ((pell_word n).get i)} := by
    ext r
    simp only [pell_nfa, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨?_, ?_, h3⟩
      · rw [Fin.ext_iff]; exact h1
      · rw [Fin.ext_iff]; simp only [Fin.val_mk]; omega
    · rintro ⟨h1, h2, h3⟩
      refine ⟨?_, ?_, h3⟩
      · rw [h1]
      · rw [h2]; simp only [Fin.val_mk]; omega
  rw [hset]
  rw [Set.encard_eq_coe_toFinset_card]
  unfold nfa_run_count_list
  rw [Set.ncard_eq_toFinset_card']
