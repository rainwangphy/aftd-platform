import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RoundRobinSequence
import AFTD.Kb.GameTheoryEconomics.IrrStep
import AFTD.Kb.GameTheoryEconomics.IsItemPreservingSwapBid
import AFTD.Kb.GameTheoryEconomics.RankingSwap
import AFTD.Kb.GameTheoryEconomics.PickingSequenceOutcome
import AFTD.Kb.GameTheoryEconomics.PickingTurn
import AFTD.Kb.Tcs.G

/-!
# iterated_round_robin_item_preserving_swaps_zero_of_card_le

Topic: fair_division   Node: 011eec5dbf95

Provenance: helper lemma. scout/2610-23040-on-the-convergence-of-iterated-round-robin.md:309

When the number of goods m is at most the number of agents n, for any initial preference profile pref : Fin n → Fin m ≃ Fin m and non-negative additive valuations v : Fin n → Fin m → ℝ (with v i g ≥ 0 for all i, g) strictly consistent with pref (with v i (pref i l) < v i (pref i k) whenever k < l), any execution f : ℕ → (Fin n → Fin m ≃ Fin m) starting at f 0 = pref of T steps of iterated Round Robin under item-preserving swap bids (irr_step) must have length T = 0.
-/

theorem iterated_round_robin_item_preserving_swaps_zero_of_card_le_seq_count_le_one
    (n m : ℕ) [NeZero n] (hm : m ≤ n) (a : Fin n) :
    (round_robin_sequence n m).count a ≤ 1 := by
  have hinj : Function.Injective (fun (t : Fin m) => (⟨t.val % n, Nat.mod_lt _ (NeZero.pos n)⟩ : Fin n)) := by
    intro x y hxy
    simp only [Fin.mk.injEq] at hxy
    have hx : x.val < n := lt_of_lt_of_le x.isLt hm
    have hy : y.val < n := lt_of_lt_of_le y.isLt hm
    rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at hxy
    ext
    exact hxy
  have hnodup : (round_robin_sequence n m).Nodup := by
    unfold round_robin_sequence
    exact List.nodup_ofFn.mpr hinj
  exact List.nodup_iff_count_le_one.mp hnodup a

theorem iterated_round_robin_item_preserving_swaps_zero_of_card_le_card_foldl_le
    {N G : Type*} [DecidableEq N] [DecidableEq G]
    (L : N → List G) (l : List N) (a : N) (st : (N → Finset G) × Finset G) :
    ((List.foldl (fun st a => picking_turn (L a) a st) st l).1 a).card ≤ (st.1 a).card + l.count a := by
  induction l generalizing st with
  | nil => simp
  | cons h t ih =>
    simp only [List.foldl_cons, List.count_cons]
    have ih_st := ih (picking_turn (L h) h st)
    have hstep : ((picking_turn (L h) h st).1 a).card ≤ (st.1 a).card + if (h == a) = true then 1 else 0 := by
      unfold picking_turn
      split
      · next g hfind =>
        dsimp only
        by_cases ha : h = a
        · subst ha
          rw [Function.update_self]
          simp only [beq_self_eq_true, ite_true]
          exact Finset.card_insert_le _ _
        · rw [Function.update_of_ne (Ne.symm ha)]
          have : (h == a) = false := beq_false_of_ne ha
          simp [this]
      · simp
    omega

/-- When m ≤ n, iterated Round Robin under item-preserving swaps terminates immediately with 0 manipulations. -/
theorem iterated_round_robin_item_preserving_swaps_zero_of_card_le (n m : ℕ) [NeZero n] (hm : m ≤ n)
    (pref : Fin n → Fin m ≃ Fin m) (v : Fin n → Fin m → ℝ) (hv : ∀ i g, 0 ≤ v i g)
    (hcons : ∀ (i : Fin n) (k l : Fin m), k < l → v i (pref i l) < v i (pref i k))
    (f : ℕ → (Fin n → Fin m ≃ Fin m)) (hf0 : f 0 = pref) (T : ℕ)
    (hf : ∀ t < T, irr_step v (round_robin_sequence n m)
      (is_item_preserving_swap_bid (round_robin_sequence n m)) (f t) (f (t + 1))) :
    T = 0 := by
  by_contra hT
  have hT0 : 0 < T := Nat.pos_of_ne_zero hT
  have hstep := hf 0 hT0
  obtain ⟨i, ⟨r, hadm, hlt⟩, -⟩ := hstep
  obtain ⟨k, l, hkl, hr, hg1, hg2⟩ := hadm
  set seq := round_robin_sequence n m
  have hcount : seq.count i ≤ 1 :=
    iterated_round_robin_item_preserving_swaps_zero_of_card_le_seq_count_le_one n m hm i
  have h0 : (((fun _ : Fin n => (∅ : Finset (Fin m))), (∅ : Finset (Fin m))).1 i).card = 0 := by simp
  have hcard1 : (picking_sequence_outcome seq (f 0) i).card ≤ 1 := by
    have hcard := iterated_round_robin_item_preserving_swaps_zero_of_card_le_card_foldl_le
      (fun a => List.ofFn (f 0 a)) seq i (fun _ => ∅, ∅)
    rw [h0] at hcard
    exact hcard.trans (by omega)
  have hcard2 : (picking_sequence_outcome seq (Function.update (f 0) i r) i).card ≤ 1 := by
    have hcard := iterated_round_robin_item_preserving_swaps_zero_of_card_le_card_foldl_le
      (fun a => List.ofFn (Function.update (f 0) i r a)) seq i (fun _ => ∅, ∅)
    rw [h0] at hcard
    exact hcard.trans (by omega)
  set g := (f 0 i) k
  have eA : picking_sequence_outcome seq (f 0) i = {g} := by
    ext x
    simp only [Finset.mem_singleton]
    exact ⟨fun hx => Finset.card_le_one.mp hcard1 x hx g hg1, fun hx => hx ▸ hg1⟩
  have eB : picking_sequence_outcome seq (Function.update (f 0) i r) i = {g} := by
    ext x
    simp only [Finset.mem_singleton]
    exact ⟨fun hx => Finset.card_le_one.mp hcard2 x hx g hg2, fun hx => hx ▸ hg2⟩
  rw [eA, eB] at hlt
  exact lt_irrefl _ hlt
