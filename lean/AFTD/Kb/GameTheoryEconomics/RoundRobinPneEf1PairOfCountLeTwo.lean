import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsPickingSequencePne
import AFTD.Kb.GameTheoryEconomics.PickingSequenceOutcome
import AFTD.Kb.GameTheoryEconomics.RoundRobinSequence
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveValuationToValuation
import AFTD.Kb.GameTheoryEconomics.RoundRobinPneEf1OfCardLeTwoMul
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveValuation
import AFTD.Kb.GameTheoryEconomics.PickingTurn

/-!
# round_robin_pne_ef1_pair_of_count_le_two

Topic: fair_division   Node: 7828f78a16a2

Provenance: helper lemma. Step for round_robin_pne_ef1_of_card_le_two_mul_add_one (thread RT-3): the argument of round_robin_pne_ef1_of_card_le_two_mul needs only that j picks at most twice.

In a pure Nash equilibrium of Round-Robin (nonnegative additive valuations), agent i is EF1 towards any agent j that appears at most twice in the picking sequence.
-/

theorem round_robin_pne_ef1_pair_of_count_le_two (n m : ℕ) [NeZero n]
    (w : Fin n → Fin m → ℝ) (hw : ∀ i g, 0 ≤ w i g) (rank : Fin n → Fin m ≃ Fin m)
    (h : is_picking_sequence_pne
      (SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation ⟨w⟩)
      (round_robin_sequence n m) rank)
    (i j : Fin n) (hij : i ≠ j) (hj : (round_robin_sequence n m).count j ≤ 2)
    (hne : (picking_sequence_outcome (round_robin_sequence n m) rank j).Nonempty) :
    ∃ g ∈ picking_sequence_outcome (round_robin_sequence n m) rank j,
      (SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation ⟨w⟩).val i
          (picking_sequence_outcome (round_robin_sequence n m) rank j \ {g}) ≤
        (SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation ⟨w⟩).val i
          (picking_sequence_outcome (round_robin_sequence n m) rank i) := by
  simp only [SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation]
  set seq := round_robin_sequence n m with hseq
  set L : Fin n → List (Fin m) := fun a => List.ofFn (rank a) with hL
  set init : (Fin n → Finset (Fin m)) × Finset (Fin m) := (fun _ => ∅, ∅) with hinit
  have hA : ∀ a, picking_sequence_outcome seq rank a =
      (seq.foldl (fun st a => picking_turn (L a) a st) init).1 a := fun a => rfl
  set A := picking_sequence_outcome seq rank with hAdef
  have hpos : ∀ S : Finset (Fin m), 0 ≤ ∑ g ∈ S, w i g := fun S => Finset.sum_nonneg (fun g _ => hw i g)
  by_cases hc : (A j).card ≤ 1
  · obtain ⟨g, hg⟩ := hne
    refine ⟨g, hg, ?_⟩
    have : A j \ {g} = ∅ := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and,
        not_not]
      intro hx
      exact Finset.card_le_one.mp hc x hx g hg
    rw [this, Finset.sum_empty]
    exact hpos _
  rw [not_le] at hc
  -- the count of `j` in the sequence bounds its bundle
  have hinit_inv : rr_l1_inv init := by
    refine ⟨fun a => by simp [hinit], fun g hg => by simp [hinit] at hg, fun a b _ => by simp [hinit]⟩
  have hcardA : (A j).card ≤ seq.count j := by
    have := rr_l1_card_foldl L seq j init
    simpa [hinit, hA] using this
  have hcount2 : seq.count j ≤ 2 := hj
  -- so agents get their first turn before the sequence ends: n < m
  have hnm : n < m := by
    by_contra hcon
    rw [not_lt] at hcon
    have hle := rr_l1_count_take_le_one n m n le_rfl j
    rw [← hseq, List.take_of_length_le (by rw [hseq, rr_l1_seq_length]; exact hcon)] at hle
    omega
  have hi_lt : i.val < seq.length := by rw [rr_l1_seq_length]; omega
  -- the state before agent i's first turn
  set st0 := (seq.take i.val).foldl (fun st a => picking_turn (L a) a st) init with hst0
  have hst0_card : (st0.1 j).card ≤ 1 := by
    have h1 := rr_l1_card_foldl L (seq.take i.val) j init
    rw [← hst0] at h1
    have h0 : (init.1 j).card = 0 := by simp [hinit]
    have h2 := rr_l1_count_take_le_one n m i.val i.isLt.le j
    rw [← hseq] at h2
    omega
  have hsplit : seq = seq.take i.val ++ (seq[i.val] :: seq.drop (i.val + 1)) := by
    rw [← List.drop_eq_getElem_cons hi_lt, List.take_append_drop]
  have hseqi : seq[i.val] = i := by
    apply Fin.ext
    rw [rr_l1_seq_getElem, Nat.mod_eq_of_lt i.isLt]
  have hrest : ∀ a, st0.1 a ⊆ A a := by
    intro a
    rw [hA, hsplit, List.foldl_append]
    exact rr_l1_mono_foldl L _ a st0
  -- a good of `A j` not yet taken before agent i's first turn
  obtain ⟨b, hbA, hb0⟩ : ∃ b ∈ A j, b ∉ st0.1 j := by
    by_contra hcon
    have hsub0 : A j ⊆ st0.1 j := fun x hx => by
      by_contra hx'
      exact hcon ⟨x, hx, hx'⟩
    have := Finset.card_le_card hsub0
    omega
  have hinvA : rr_l1_inv (seq.foldl (fun st a => picking_turn (L a) a st) init) :=
    rr_l1_inv_foldl L seq init hinit_inv
  have hinv0 : rr_l1_inv st0 := rr_l1_inv_foldl L _ init hinit_inv
  have hbfree : b ∉ st0.2 := by
    intro hb
    obtain ⟨a, ha⟩ := hinv0.2.1 b hb
    by_cases haj : a = j
    · subst haj; exact hb0 ha
    · have hd := hinvA.2.2 a j haj
      rw [← hA, ← hA] at hd
      exact Finset.disjoint_left.mp hd (hrest a ha) hbA
  -- the deviation: rank `b` first
  have hm0 : 0 < m := by omega
  set r' : Fin m ≃ Fin m := Equiv.swap ⟨0, hm0⟩ b with hr'
  have hr'0 : r' ⟨0, hm0⟩ = b := by simp [hr']
  have hdev : b ∈ picking_sequence_outcome seq (Function.update rank i r') i := by
    have hL' : (fun st a => picking_turn (List.ofFn (Function.update rank i r' a)) a st) =
        (fun st a => picking_turn (Function.update L i (List.ofFn r') a) a st) := by
      funext st a
      by_cases ha : a = i
      · subst ha; simp
      · simp [Function.update_of_ne ha, hL]
    show b ∈ (seq.foldl (fun st a => picking_turn (List.ofFn (Function.update rank i r' a)) a st) init).1 i
    rw [hL', hsplit, List.foldl_append, rr_l1_foldl_update L _ i _ ?_ init, List.foldl_cons, hseqi]
    · rw [← hst0]
      apply rr_l1_mono_foldl
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hfind : (List.ofFn r').find? (fun g => decide (g ∉ st0.2)) = some b := by
        rw [List.ofFn_succ, List.find?_cons]
        have : r' 0 = b := hr'0
        rw [this]
        simp [hbfree]
      simp only [Function.update_self, picking_turn, hfind, Function.update_self]
      exact Finset.mem_insert_self _ _
    · intro x hx
      obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.mp hx
      intro hti
      have h1 := congrArg Fin.val hti
      have h2 : ((seq.take i.val)[t]'ht).val = t % n := by
        rw [List.getElem_take]; exact rr_l1_seq_getElem n m t _
      rw [h2] at h1
      simp only [List.length_take] at ht
      rw [Nat.mod_eq_of_lt (by omega)] at h1
      omega
  -- conclude with the other good of `A j`
  obtain ⟨a, haA, hab⟩ := Finset.exists_mem_ne hc b
  refine ⟨a, haA, ?_⟩
  have hsub : A j \ {a} = {b} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨Finset.mem_sdiff.mpr ⟨hbA, by simpa using Ne.symm hab⟩, fun x hx => ?_⟩
    obtain ⟨hxA, hxa⟩ := Finset.mem_sdiff.mp hx
    by_contra hxb
    have h3 : ({a, b, x} : Finset (Fin m)) ⊆ A j := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl <;> assumption
    have h4 := Finset.card_le_card h3
    rw [Finset.card_insert_of_notMem (by simp [hab, Ne.symm (show x ≠ a by simpa using hxa)]),
      Finset.card_insert_of_notMem (by simpa using Ne.symm hxb), Finset.card_singleton] at h4
    omega
  rw [hsub, Finset.sum_singleton]
  have hpne := h i r'
  simp only [SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation] at hpne
  have hb_le : w i b ≤ ∑ g ∈ picking_sequence_outcome seq (Function.update rank i r') i, w i g :=
    Finset.single_le_sum (fun g _ => hw i g) hdev
  exact hb_le.trans hpne
