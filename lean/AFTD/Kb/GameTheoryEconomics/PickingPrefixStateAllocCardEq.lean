import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PickingPrefixState
import AFTD.Kb.GameTheoryEconomics.PickingTurn
import AFTD.Kb.Tcs.G

/-!
# picking_prefix_state_alloc_card_eq

Topic: fair_division   Node: 940c76ad3a15

Provenance: helper lemma. step towards round_robin_two_mul_add_one_deviation_certificate

After s turns of a picking sequence with at most as many turns as goods, exactly min s (length seq) goods have been allocated (in particular exactly s for s <= length seq).
-/

theorem picking_prefix_state_alloc_card_eq_turn {N G : Type*} [DecidableEq N] [DecidableEq G]
    [Fintype G] {m : ℕ} (r : Fin m ≃ G) (a : N) (st : (N → Finset G) × Finset G)
    (hst : st.2.card < m) :
    (picking_turn (List.ofFn ⇑r) a st).2.card = st.2.card + 1 := by
  have hcardG : Fintype.card G = m := by simpa using (Fintype.card_congr r).symm
  obtain ⟨g, hg⟩ : ∃ g : G, g ∉ st.2 := by
    by_contra hc
    push Not at hc
    have : (Finset.univ : Finset G) ⊆ st.2 := fun x _ => hc x
    have := Finset.card_le_card this
    rw [Finset.card_univ, hcardG] at this
    omega
  dsimp [picking_turn]
  split
  · next g' hfind =>
    have := List.find?_some hfind
    simp only [decide_eq_true_eq] at this
    rw [Finset.card_insert_of_notMem this]
  · next hfind =>
    exfalso
    rw [List.find?_eq_none] at hfind
    have hmem : g ∈ List.ofFn ⇑r := by
      rw [List.mem_ofFn]
      exact ⟨r.symm g, by simp⟩
    have := hfind g hmem
    simp only [decide_eq_true_eq, not_not] at this
    exact hg this

/-- After s turns of a picking sequence with at most as many turns as goods, exactly min s (length seq) goods are allocated. -/
theorem picking_prefix_state_alloc_card_eq {N G : Type*} [DecidableEq N] [DecidableEq G] [Fintype G]
    {m : ℕ} (seq : List N) (rank : N → Fin m ≃ G) (s : ℕ) (hseq : seq.length ≤ m) :
    (picking_prefix_state seq rank s).2.card = min s seq.length := by
  induction s with
  | zero => simp [picking_prefix_state]
  | succ t ih =>
    have hstep : picking_prefix_state seq rank (t + 1) =
        (seq.take t ++ seq[t]?.toList).foldl
          (fun st a => picking_turn (List.ofFn ⇑(rank a)) a st) (fun _ => ∅, ∅) := by
      unfold picking_prefix_state; rw [List.take_add_one]
    rcases h : seq[t]? with _ | a
    · rw [hstep, h, Option.toList_none, List.append_nil]
      change (picking_prefix_state seq rank t).2.card = _
      rw [ih]
      have : seq.length ≤ t := by
        by_contra hc; push Not at hc
        rw [List.getElem?_eq_getElem hc] at h; simp at h
      omega
    · rw [hstep, h, Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have ht : t < seq.length := by
        by_contra hc; push Not at hc
        rw [List.getElem?_eq_none hc] at h; simp at h
      change (picking_turn (List.ofFn ⇑(rank a)) a (picking_prefix_state seq rank t)).2.card = _
      rw [picking_prefix_state_alloc_card_eq_turn (rank a) a _ (by rw [ih]; omega), ih]
      omega
