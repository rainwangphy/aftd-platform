import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CatchUpValueAux
import AFTD.Kb.GameTheoryEconomics.CatchUpEvalList
import AFTD.Kb.GameTheoryEconomics.CatchUpBestAttachMapCongr
import AFTD.Kb.GameTheoryEconomics.CatchUpToFinsetErase

/-!
# catch_up_value_aux_eq_eval_list

Topic: combinatorial_games   Node: 6b45afbb5db1

For every fuel n, every duplicate-free list l of length at most n, and all scores and opening flags, the Catch-Up value of the finset of l equals the computable mirror catch_up_eval_list n l.
-/

/-- The computable mirror agrees with `catch_up_value_aux` whenever the fuel covers the list. -/
theorem catch_up_value_aux_eq_eval_list (n : ℕ) :
    ∀ (l : List ℕ), l.Nodup → l.length ≤ n → ∀ (s_me s_opp : ℕ) (first : Bool),
      catch_up_value_aux l.toFinset s_me s_opp first = catch_up_eval_list n l s_me s_opp first := by
  induction n with
  | zero =>
    intro l _ hlen s_me s_opp first
    have : l = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    rw [catch_up_value_aux.eq_def]
    simp [catch_up_eval_list]
  | succ n ih =>
    intro l hl hlen s_me s_opp first
    cases l with
    | nil =>
      rw [catch_up_value_aux.eq_def]
      simp [catch_up_eval_list]
    | cons h t =>
      rw [catch_up_value_aux.eq_def]
      have hne : (h :: t).toFinset ≠ ∅ := by simp
      have hsum : (h :: t).toFinset.sum (fun x => x) = (h :: t).sum := by
        rw [List.sum_toFinset _ hl, List.map_id']
      simp only [hne, if_false, hsum, catch_up_eval_list]
      by_cases hlt : s_me + (h :: t).sum < s_opp
      · simp only [hlt, if_true]
      · simp only [hlt, if_false]
        refine catch_up_best_attach_map_congr (h :: t)
          (fun y => if first = true then
              (catch_up_value_aux ((h :: t).toFinset.erase y) s_opp (s_me + y) false).neg
            else if s_me + y ≥ s_opp then
              (catch_up_value_aux ((h :: t).toFinset.erase y) s_opp (s_me + y) false).neg
            else catch_up_value_aux ((h :: t).toFinset.erase y) (s_me + y) s_opp false)
          (fun y => if first = true then
              (catch_up_eval_list n ((h :: t).erase y) s_opp (s_me + y) false).neg
            else if s_me + y ≥ s_opp then
              (catch_up_eval_list n ((h :: t).erase y) s_opp (s_me + y) false).neg
            else catch_up_eval_list n ((h :: t).erase y) (s_me + y) s_opp false) ?_
        intro x hx
        have hlen' : ((h :: t).erase x).length ≤ n := by
          rw [List.length_erase_of_mem hx]; simp at hlen ⊢; omega
        simp only [catch_up_toFinset_erase hl, ih _ (hl.erase x) hlen']
