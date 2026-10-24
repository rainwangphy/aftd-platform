import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PickingPrefixStateAllocCardEq
import AFTD.Kb.GameTheoryEconomics.PickingPrefixState
import AFTD.Kb.GameTheoryEconomics.PickingTurn

/-!
# picking_prefix_state_succ_step

Topic: fair_division   Node: 1c69fad07a86

Provenance: helper lemma. step towards round_robin_two_mul_add_one_deviation_certificate

Turn s of a picking sequence with s < length seq and s < m: if the active agent is a, there is a good p, not allocated after s turns, such that after s+1 turns the allocated set is insert p (allocated after s), the bundle of a grows by exactly p, every other bundle is unchanged, and every good ranked before p by a is already allocated.
-/

theorem picking_prefix_state_succ_step_card_le {N G : Type*} [DecidableEq N] [DecidableEq G]
    {m : ℕ} (seq : List N) (rank : N → Fin m ≃ G) (s : ℕ) :
    (picking_prefix_state seq rank s).2.card ≤ s := by
  induction s with
  | zero => simp [picking_prefix_state]
  | succ t ih =>
    have hstep : picking_prefix_state seq rank (t + 1) =
        (seq.take t ++ seq[t]?.toList).foldl
          (fun st a => picking_turn (List.ofFn ⇑(rank a)) a st) (fun _ => ∅, ∅) := by
      unfold picking_prefix_state; rw [List.take_add_one]
    rcases h : seq[t]? with _ | a
    · rw [hstep, h, Option.toList_none, List.append_nil]
      change (picking_prefix_state seq rank t).2.card ≤ _
      omega
    · rw [hstep, h, Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil]
      change (picking_turn (List.ofFn ⇑(rank a)) a (picking_prefix_state seq rank t)).2.card ≤ _
      dsimp [picking_turn]
      split
      · exact (Finset.card_insert_le _ _).trans (by omega)
      · omega

/-- One turn of a picking sequence allocates exactly one good, namely the first good of the active agent's ranking that is not yet allocated. -/
theorem picking_prefix_state_succ_step {N G : Type*} [DecidableEq N] [DecidableEq G] [Fintype G]
    {m : ℕ} (seq : List N) (rank : N → Fin m ≃ G) (s : ℕ) (hsl : s < seq.length) (hsm : s < m)
    (a : N) (ha : seq[s]? = some a) :
    ∃ p : G, p ∉ (picking_prefix_state seq rank s).2 ∧
      (picking_prefix_state seq rank (s + 1)).2 = insert p (picking_prefix_state seq rank s).2 ∧
      (picking_prefix_state seq rank (s + 1)).1 a = insert p ((picking_prefix_state seq rank s).1 a) ∧
      (∀ b : N, b ≠ a → (picking_prefix_state seq rank (s + 1)).1 b =
        (picking_prefix_state seq rank s).1 b) ∧
      (∃ k : Fin m, (rank a) k = p ∧ ∀ j : Fin m, j < k → (rank a) j ∈ (picking_prefix_state seq rank s).2) := by
  have hstep : picking_prefix_state seq rank (s + 1) =
      picking_turn (List.ofFn ⇑(rank a)) a (picking_prefix_state seq rank s) := by
    unfold picking_prefix_state
    rw [List.take_add_one, ha, Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hcs := picking_prefix_state_succ_step_card_le seq rank s
  set st := picking_prefix_state seq rank s with hst
  have hcardG : Fintype.card G = m := by simpa using (Fintype.card_congr (rank a)).symm
  obtain ⟨g, hg⟩ : ∃ g : G, g ∉ st.2 := by
    by_contra hc
    push Not at hc
    have : (Finset.univ : Finset G) ⊆ st.2 := fun x _ => hc x
    have := Finset.card_le_card this
    rw [Finset.card_univ, hcardG] at this
    omega
  rw [hstep]
  rcases hfind : (List.ofFn ⇑(rank a)).find? (fun g => decide (g ∉ st.2)) with _ | p
  · exfalso
    rw [List.find?_eq_none] at hfind
    have hmem : g ∈ List.ofFn ⇑(rank a) := by
      rw [List.mem_ofFn]
      exact ⟨(rank a).symm g, by simp⟩
    have := hfind g hmem
    simp only [decide_eq_true_eq, not_not] at this
    exact hg this
  · have hf := hfind
    rw [List.find?_eq_some_iff_getElem] at hf
    obtain ⟨hp, i, hi, hip, hbefore⟩ := hf
    simp only [decide_eq_true_eq] at hp
    rw [List.length_ofFn] at hi
    have hpt : picking_turn (List.ofFn ⇑(rank a)) a st =
        (Function.update st.1 a (insert p (st.1 a)), insert p st.2) := by
      unfold picking_turn; rw [hfind]
    rw [hpt]
    refine ⟨p, hp, rfl, ?_, ?_, ⟨i, hi⟩, ?_, ?_⟩
    · simp
    · intro b hb
      simp [Function.update_of_ne hb]
    · rw [← hip]; simp
    · intro j hj
      have := hbefore j.val (by exact_mod_cast hj)
      simp only [List.getElem_ofFn, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not,
        not_not] at this
      simpa using this
