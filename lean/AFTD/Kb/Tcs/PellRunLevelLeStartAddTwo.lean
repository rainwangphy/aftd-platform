import AFTD.Prelude
import AFTD.Kb.Tcs.PellNfa
import AFTD.Kb.Tcs.PellNfaStepTable

/-!
# pell_run_level_le_start_add_two

Topic: automata   Node: 619a58cdcee0

Provenance: helper lemma. step towards optimal_asymptotic_base_constant_finitely_ambiguous_nfa

In the Pell automaton A_n, if a run starting at state p reads only letters congruent to c_p or to c_{p+1} (mod 5), then at every time its state is one of p, p+1, p+2 — equivalently the state index never exceeds (index of p) + 2.
-/

/-- Structural fact behind finite ambiguity of the Pell automaton: a run that only ever reads letters congruent to c_p or c_{p+1} (mod 5) never climbs above the state two places beyond its starting state. -/
theorem pell_run_level_le_start_add_two (n : ℕ) (w : List (Fin 5))
    (r : Fin (w.length + 1) → Fin n)
    (hr : ∀ i : Fin w.length, r i.succ ∈ (pell_nfa n).step (r i.castSucc) (w.get i))
    (hw : ∀ i : Fin w.length, (w.get i).val = (r 0).val % 5 ∨ (w.get i).val = ((r 0).val + 1) % 5)
    (i : Fin (w.length + 1)) : (r i).val ≤ (r 0).val + 2 := by
  have main : ∀ i : Fin (w.length + 1), (r i).val ≤ (r 0).val + 2 := by
    intro i
    induction i using Fin.induction with
    | zero => simp
    | succ j ih =>
      have hs := pell_nfa_step_table n (hr j)
      have hwj := hw j
      rcases hs with ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩ | ⟨h1, h2 | h2⟩ <;>
        simp only [h1, h2] at * <;> omega
  exact main i
