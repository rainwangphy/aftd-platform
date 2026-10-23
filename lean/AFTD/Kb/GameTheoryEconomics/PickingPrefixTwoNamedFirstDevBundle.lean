import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PickingSequenceOutcomeUpdateMemOfFirstFree
import AFTD.Kb.GameTheoryEconomics.PickingPrefixStateUpdateOfNotMemTake
import AFTD.Kb.GameTheoryEconomics.PickingSequenceOutcome
import AFTD.Kb.GameTheoryEconomics.PickingPrefixState
import AFTD.Kb.GameTheoryEconomics.PickingTurn
import AFTD.Kb.Tcs.G

/-!
# picking_prefix_two_named_first_dev_bundle

Topic: fair_division   Node: 2fa4f5a1a5a4

Provenance: helper lemma. step towards round_robin_two_mul_add_one_deviation_certificate

In a picking sequence with at most as many turns as goods, suppose agent i acts at turns t1 < t2 and nowhere in between, x is unallocated at t1 in the original run and y is unallocated at t2 in the run where i reports r (r ranks x first, y second). Then that run gives agent i both x and y.
-/

theorem picking_prefix_two_named_first_dev_bundle_step {N G : Type*} [DecidableEq N]
    [DecidableEq G] {m : ℕ} (seq : List N) (rank : N → Fin m ≃ G) (s : ℕ) (a : N)
    (h : seq[s]? = some a) :
    picking_prefix_state seq rank (s + 1) =
      picking_turn (List.ofFn ⇑(rank a)) a (picking_prefix_state seq rank s) := by
  unfold picking_prefix_state
  rw [List.take_add_one, h, Option.toList_some, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem picking_prefix_two_named_first_dev_bundle_step_none {N G : Type*} [DecidableEq N]
    [DecidableEq G] {m : ℕ} (seq : List N) (rank : N → Fin m ≃ G) (s : ℕ)
    (h : seq[s]? = none) :
    picking_prefix_state seq rank (s + 1) = picking_prefix_state seq rank s := by
  unfold picking_prefix_state
  rw [List.take_add_one, h, Option.toList_none, List.append_nil]

theorem picking_prefix_two_named_first_dev_bundle_turn_mono {N G : Type*} [DecidableEq N]
    [DecidableEq G] (l : List G) (a : N) (st : (N → Finset G) × Finset G) :
    (∀ j, st.1 j ⊆ (picking_turn l a st).1 j) ∧ st.2 ⊆ (picking_turn l a st).2 := by
  constructor
  · intro j g hg
    exact picking_sequence_outcome_update_mem_of_first_free_mem_turn_bundle l a st j g hg
  · intro g hg
    dsimp [picking_turn]
    split
    · exact Finset.mem_insert_of_mem hg
    · exact hg

theorem picking_prefix_two_named_first_dev_bundle_mono {N G : Type*} [DecidableEq N]
    [DecidableEq G] {m : ℕ} (seq : List N) (rank : N → Fin m ≃ G) (s t : ℕ) (hst : s ≤ t) :
    (∀ j, (picking_prefix_state seq rank s).1 j ⊆ (picking_prefix_state seq rank t).1 j) ∧
      (picking_prefix_state seq rank s).2 ⊆ (picking_prefix_state seq rank t).2 := by
  induction t, hst using Nat.le_induction with
  | base => exact ⟨fun _ => subset_refl _, subset_refl _⟩
  | succ t _ ih =>
    rcases h : seq[t]? with _ | a
    · rw [picking_prefix_two_named_first_dev_bundle_step_none seq rank t h]
      exact ih
    · rw [picking_prefix_two_named_first_dev_bundle_step seq rank t a h]
      obtain ⟨h1, h2⟩ := picking_prefix_two_named_first_dev_bundle_turn_mono
        (List.ofFn ⇑(rank a)) a (picking_prefix_state seq rank t)
      exact ⟨fun j => (ih.1 j).trans (h1 j), ih.2.trans h2⟩

theorem picking_prefix_two_named_first_dev_bundle_sub_alloc {N G : Type*} [DecidableEq N]
    [DecidableEq G] {m : ℕ} (seq : List N) (rank : N → Fin m ≃ G) (s : ℕ) (j : N) :
    (picking_prefix_state seq rank s).1 j ⊆ (picking_prefix_state seq rank s).2 := by
  induction s with
  | zero => simp [picking_prefix_state]
  | succ t ih =>
    rcases h : seq[t]? with _ | a
    · rw [picking_prefix_two_named_first_dev_bundle_step_none seq rank t h]
      exact ih
    · rw [picking_prefix_two_named_first_dev_bundle_step seq rank t a h]
      intro g hg
      dsimp [picking_turn] at hg ⊢
      split at hg
      · next g' _ =>
        dsimp only at hg ⊢
        by_cases hja : j = a
        · subst hja
          rw [Function.update_self, Finset.mem_insert] at hg
          rcases hg with rfl | hg
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (ih hg)
        · rw [Function.update_of_ne hja] at hg
          exact Finset.mem_insert_of_mem (ih hg)
      · exact ih hg

theorem picking_prefix_two_named_first_dev_bundle_turn_second {N G : Type*} [DecidableEq N]
    [DecidableEq G] {m : ℕ} (r : Fin m ≃ G) (hm : 1 < m) (i : N) (st : (N → Finset G) × Finset G)
    (h0 : r ⟨0, by omega⟩ ∈ st.2) (h1 : r ⟨1, hm⟩ ∉ st.2) :
    r ⟨1, hm⟩ ∈ (picking_turn (List.ofFn (r : Fin m → G)) i st).1 i := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have e0 : (⟨0, by omega⟩ : Fin (k + 2)) = 0 := rfl
  have e1 : (⟨1, hm⟩ : Fin (k + 2)) = 1 := rfl
  rw [e0] at h0
  rw [e1] at h1 ⊢
  rw [List.ofFn_succ, List.ofFn_succ]
  dsimp [picking_turn]
  have hd0 : decide (r 0 ∉ st.2) = false := decide_eq_false (not_not.mpr h0)
  have hd1 : decide (r 1 ∉ st.2) = true := decide_eq_true h1
  rw [List.find?_cons, hd0]
  dsimp only
  rw [List.find?_cons, hd1]
  dsimp only
  rw [Function.update_self]
  exact Finset.mem_insert_self _ _

/-- If agent i reports x first and y second, x is still free at its first turn and y is still free at its second turn, then i's bundle in that run contains both x and y. -/
theorem picking_prefix_two_named_first_dev_bundle {N G : Type*} [DecidableEq N] [DecidableEq G] [Fintype G]
    {m : ℕ} (seq : List N) (rank : N → Fin m ≃ G) (r : Fin m ≃ G) (i : N) (t₁ t₂ : ℕ)
    (hm : 1 < m) (hseq : seq.length ≤ m)
    (h₁ : seq[t₁]? = some i) (h₂ : seq[t₂]? = some i) (hlt : t₁ < t₂)
    (x y : G) (hx : x ∉ (picking_prefix_state seq rank t₁).2)
    (hy : y ∉ (picking_prefix_state seq (Function.update rank i r) t₂).2)
    (h0 : r ⟨0, by omega⟩ = x) (h1 : r ⟨1, hm⟩ = y) :
    ({x, y} : Finset G) ⊆ picking_sequence_outcome seq (Function.update rank i r) i := by
  classical
  set rank' := Function.update rank i r with hrank'
  -- the outcome is the state after all turns
  have hout : picking_sequence_outcome seq rank' = (picking_prefix_state seq rank' seq.length).1 := by
    unfold picking_sequence_outcome picking_prefix_state
    rw [List.take_length]
  have ht2 : t₂ < seq.length := (List.getElem?_eq_some_iff.mp h₂).1
  -- i's first turn
  have hex : ∃ t, seq[t]? = some i := ⟨t₁, h₁⟩
  let t₀ := Nat.find hex
  have ht₀ : seq[t₀]? = some i := Nat.find_spec hex
  have ht₀le : t₀ ≤ t₁ := Nat.find_min' hex h₁
  have hnot : i ∉ seq.take t₀ := by
    intro hmem
    obtain ⟨k, hk, hki⟩ := List.getElem_of_mem hmem
    rw [List.length_take] at hk
    have hk' : k < t₀ := lt_of_lt_of_le hk (min_le_left _ _)
    apply Nat.find_min hex hk'
    rw [List.getElem_take] at hki
    rw [List.getElem?_eq_getElem (by omega), hki]
  have hfree : r ⟨0, by omega⟩ ∉ (picking_prefix_state seq rank t₀).2 := by
    rw [h0]
    intro hc
    exact hx ((picking_prefix_two_named_first_dev_bundle_mono seq rank t₀ t₁ ht₀le).2 hc)
  -- x is in i's bundle right after turn t₀ of the deviated run
  have hpre : picking_prefix_state seq rank' t₀ = picking_prefix_state seq rank t₀ :=
    picking_prefix_state_update_of_not_mem_take seq rank i r t₀ hnot
  have hri : rank' i = r := Function.update_self i r rank
  have hx1 : x ∈ (picking_prefix_state seq rank' (t₀ + 1)).1 i := by
    rw [picking_prefix_two_named_first_dev_bundle_step seq rank' t₀ i ht₀, hpre, hri, ← h0]
    exact picking_sequence_outcome_update_mem_of_first_free_turn_first_free r (by omega) i _ hfree
  have hx2 : x ∈ (picking_prefix_state seq rank' t₂).1 i :=
    (picking_prefix_two_named_first_dev_bundle_mono seq rank' (t₀ + 1) t₂ (by omega)).1 i hx1
  have hxa : x ∈ (picking_prefix_state seq rank' t₂).2 :=
    picking_prefix_two_named_first_dev_bundle_sub_alloc seq rank' t₂ i hx2
  have hy1 : y ∈ (picking_prefix_state seq rank' (t₂ + 1)).1 i := by
    rw [picking_prefix_two_named_first_dev_bundle_step seq rank' t₂ i h₂, hri, ← h1]
    exact picking_prefix_two_named_first_dev_bundle_turn_second r hm i _ (by rw [h0]; exact hxa)
      (by rw [h1]; exact hy)
  have hmono := (picking_prefix_two_named_first_dev_bundle_mono seq rank' (t₂ + 1) seq.length
    (by omega)).1 i
  have hmono0 := (picking_prefix_two_named_first_dev_bundle_mono seq rank' (t₀ + 1) seq.length
    (by omega)).1 i
  rw [hout]
  intro g hg
  rw [Finset.mem_insert, Finset.mem_singleton] at hg
  rcases hg with rfl | rfl
  · exact hmono0 hx1
  · exact hmono hy1
