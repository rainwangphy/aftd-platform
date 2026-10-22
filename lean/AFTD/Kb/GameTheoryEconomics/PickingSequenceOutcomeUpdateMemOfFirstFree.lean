import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PickingSequenceOutcome
import AFTD.Kb.GameTheoryEconomics.PickingPrefixState
import AFTD.Kb.GameTheoryEconomics.PickingTurn
import AFTD.Kb.GameTheoryEconomics.PickingPrefixStateUpdateOfNotMemTake

/-!
# picking_sequence_outcome_update_mem_of_first_free

Topic: fair_division   Node: 1bdf322af1d3

Provenance: helper lemma. Step toward round_robin_two_mul_add_one_deviation_certificate (thread RT-3): the first case of the journal's turn analysis (agent i reporting a2 first gets a2).

In a picking-sequence run, if agent i's first turn is turn t and the good g that i's new report r ranks first is still unallocated after the first t turns of the original run, then i gets g when it reports r (the others' reports unchanged).
-/

theorem picking_sequence_outcome_update_mem_of_first_free_mem_turn_bundle
    {N G : Type*} [DecidableEq N] [DecidableEq G]
    (l : List G) (a : N) (st : (N → Finset G) × Finset G) (i : N) (g : G)
    (hg : g ∈ st.1 i) :
    g ∈ (picking_turn l a st).1 i := by
  dsimp [picking_turn]
  split
  · next g' hfind =>
    dsimp only
    by_cases hai : a = i
    · subst hai
      rw [Function.update_self]
      exact Finset.mem_insert_of_mem hg
    · rw [Function.update_of_ne (Ne.symm hai)]
      exact hg
  · exact hg

theorem picking_sequence_outcome_update_mem_of_first_free_mem_foldl_turn_bundle
    {N G : Type*} [DecidableEq N] [DecidableEq G]
    (f : N → List G) (tail : List N) (st : (N → Finset G) × Finset G) (i : N) (g : G)
    (hg : g ∈ st.1 i) :
    g ∈ (tail.foldl (fun s a => picking_turn (f a) a s) st).1 i := by
  induction tail generalizing st with
  | nil => exact hg
  | cons a as ih =>
    exact ih (picking_turn (f a) a st)
      (picking_sequence_outcome_update_mem_of_first_free_mem_turn_bundle (f a) a st i g hg)

theorem picking_sequence_outcome_update_mem_of_first_free_turn_first_free
    {N G : Type*} [DecidableEq N] [DecidableEq G]
    {m : ℕ} (r : Fin m ≃ G) (hm : 0 < m) (i : N) (st : (N → Finset G) × Finset G)
    (hfree : r ⟨0, hm⟩ ∉ st.2) :
    r ⟨0, hm⟩ ∈ (picking_turn (List.ofFn (r : Fin m → G)) i st).1 i := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  have hr0 : (⟨0, hm⟩ : Fin (k + 1)) = 0 := rfl
  rw [hr0] at hfree ⊢
  rw [List.ofFn_succ]
  dsimp [picking_turn]
  have hdec : decide (r 0 ∉ st.2) = true := decide_eq_true hfree
  rw [List.find?_cons, hdec]
  dsimp only
  rw [Function.update_self]
  exact Finset.mem_insert_self (r 0) (st.1 i)

theorem picking_sequence_outcome_update_mem_of_first_free {N G : Type*} [DecidableEq N]
    [DecidableEq G] {m : ℕ} (seq : List N) (rank : N → Fin m ≃ G) (i : N) (r : Fin m ≃ G)
    (t : ℕ) (hit : seq[t]? = some i) (hnot : i ∉ seq.take t) (hm : 0 < m)
    (hfree : r ⟨0, hm⟩ ∉ (picking_prefix_state seq rank t).2) :
    r ⟨0, hm⟩ ∈ picking_sequence_outcome seq (Function.update rank i r) i := by
  set rank' := Function.update rank i r
  have h_drop : seq.drop t = i :: seq.drop (t + 1) := by
    obtain ⟨ht, h_get⟩ := List.getElem?_eq_some_iff.mp hit
    rw [← h_get]
    exact List.cons_getElem_drop_succ.symm
  have h_seq : seq = seq.take t ++ (i :: seq.drop (t + 1)) := by
    conv_lhs => rw [← List.take_append_drop t seq]
    rw [h_drop]
  dsimp [picking_sequence_outcome]
  rw [h_seq, List.foldl_append, List.foldl_cons]
  have h_pref : (seq.take t).foldl (fun st a => picking_turn (List.ofFn ⇑(rank' a)) a st) (fun x => ∅, ∅)
      = picking_prefix_state seq rank t := by
    change picking_prefix_state seq rank' t = picking_prefix_state seq rank t
    exact picking_prefix_state_update_of_not_mem_take seq rank i r t hnot
  rw [h_pref]
  have h_rank'i : rank' i = r := Function.update_self i r rank
  rw [h_rank'i]
  have h_in : r ⟨0, hm⟩ ∈ (picking_turn (List.ofFn ⇑r) i (picking_prefix_state seq rank t)).1 i :=
    picking_sequence_outcome_update_mem_of_first_free_turn_first_free r hm i (picking_prefix_state seq rank t) hfree
  exact picking_sequence_outcome_update_mem_of_first_free_mem_foldl_turn_bundle
    (fun a => List.ofFn ⇑(rank' a)) (seq.drop (t + 1)) _ i _ h_in
