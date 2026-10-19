import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsPickingSequencePne
import AFTD.Kb.GameTheoryEconomics.PickingSequenceOutcome
import AFTD.Kb.GameTheoryEconomics.RoundRobinSequence
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleIsEF1
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveValuationToValuation
import AFTD.Kb.GameTheoryEconomics.PickingTurn
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveValuation
import AFTD.Kb.Tcs.G

/-!
# round_robin_pne_ef1_of_card_le_two_mul

Topic: fair_division   Node: a975f10ed7ff

Provenance: helper lemma. Step for round_robin_pne_ef1_of_card_le_two_mul_add_one (the threshold question posed from arXiv:2610.23686 Proposition 1).

With n agents and at most 2n goods (every agent picks at most twice), every pure Nash equilibrium of Round-Robin, for nonnegative additive valuations, is EF1.
-/

section rr_l1
variable {N G : Type*} [DecidableEq N] [DecidableEq G]

theorem rr_l1_turn_cases (l : List G) (i : N) (st : (N → Finset G) × Finset G) :
    picking_turn l i st = st ∨ ∃ g, g ∉ st.2 ∧
      picking_turn l i st = (Function.update st.1 i (insert g (st.1 i)), insert g st.2) := by
  unfold picking_turn
  split
  · rename_i g hg
    have := List.find?_some hg
    simp only [decide_eq_true_eq] at this
    exact Or.inr ⟨g, this, rfl⟩
  · exact Or.inl rfl

/-- Invariant of a run: bundles lie in the allocated set, cover it, and are pairwise disjoint. -/
def rr_l1_inv (st : (N → Finset G) × Finset G) : Prop :=
  (∀ a, st.1 a ⊆ st.2) ∧ (∀ g ∈ st.2, ∃ a, g ∈ st.1 a) ∧
    (∀ a b, a ≠ b → Disjoint (st.1 a) (st.1 b))

theorem rr_l1_inv_turn (l : List G) (i : N) (st : (N → Finset G) × Finset G) (h : rr_l1_inv st) :
    rr_l1_inv (picking_turn l i st) := by
  rcases rr_l1_turn_cases l i st with h' | ⟨g, hg, h'⟩
  · rw [h']; exact h
  · rw [h']
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨fun a => ?_, fun x hx => ?_, fun a b hab => ?_⟩
    · by_cases ha : a = i
      · subst ha; simp only [Function.update_self]
        exact Finset.insert_subset_insert _ (h1 a)
      · simp only [Function.update_of_ne ha]
        exact (h1 a).trans (Finset.subset_insert _ _)
    · rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨i, by simp⟩
      · obtain ⟨a, ha⟩ := h2 x hx
        refine ⟨a, ?_⟩
        by_cases hai : a = i
        · subst hai; simp [ha]
        · simp only [Function.update_of_ne hai]; exact ha
    · have key : ∀ c, c ≠ i → g ∉ st.1 c := fun c _ hc => hg (h1 c hc)
      by_cases ha : a = i
      · subst ha
        simp only [Function.update_self, Function.update_of_ne (Ne.symm hab)]
        exact Finset.disjoint_insert_left.mpr ⟨key b (Ne.symm hab), h3 a b hab⟩
      · by_cases hb : b = i
        · subst hb
          simp only [Function.update_self, Function.update_of_ne ha]
          exact Finset.disjoint_insert_right.mpr ⟨key a ha, h3 a b hab⟩
        · simp only [Function.update_of_ne ha, Function.update_of_ne hb]; exact h3 a b hab

theorem rr_l1_mono_turn (l : List G) (i : N) (st : (N → Finset G) × Finset G) (a : N) :
    st.1 a ⊆ (picking_turn l i st).1 a := by
  rcases rr_l1_turn_cases l i st with h' | ⟨g, hg, h'⟩
  · rw [h']
  · rw [h']
    by_cases ha : a = i
    · subst ha; simp only [Function.update_self]; exact Finset.subset_insert _ _
    · simp only [Function.update_of_ne ha]; exact le_rfl

theorem rr_l1_card_turn (l : List G) (i : N) (st : (N → Finset G) × Finset G) (a : N) :
    ((picking_turn l i st).1 a).card ≤ (st.1 a).card + if a = i then 1 else 0 := by
  rcases rr_l1_turn_cases l i st with h' | ⟨g, hg, h'⟩
  · rw [h']; omega
  · rw [h']
    by_cases ha : a = i
    · subst ha; simp only [Function.update_self, if_true]; exact Finset.card_insert_le _ _
    · simp only [Function.update_of_ne ha, if_neg ha]; omega

variable (L : N → List G)

theorem rr_l1_inv_foldl (l : List N) : ∀ st : (N → Finset G) × Finset G, rr_l1_inv st →
    rr_l1_inv (l.foldl (fun st a => picking_turn (L a) a st) st) := by
  induction l with
  | nil => intro st h; exact h
  | cons x l ih => intro st h; exact ih _ (rr_l1_inv_turn _ _ _ h)

theorem rr_l1_mono_foldl (l : List N) (a : N) : ∀ st : (N → Finset G) × Finset G,
    st.1 a ⊆ (l.foldl (fun st a => picking_turn (L a) a st) st).1 a := by
  induction l with
  | nil => intro st; exact le_rfl
  | cons x l ih => intro st; exact (rr_l1_mono_turn _ _ _ a).trans (ih _)

theorem rr_l1_card_foldl (l : List N) (a : N) : ∀ st : (N → Finset G) × Finset G,
    ((l.foldl (fun st a => picking_turn (L a) a st) st).1 a).card ≤ (st.1 a).card + l.count a := by
  induction l with
  | nil => intro st; simp
  | cons x l ih =>
    intro st
    simp only [List.foldl_cons, List.count_cons]
    refine (ih _).trans ?_
    have := rr_l1_card_turn (L x) x st a
    by_cases hax : a = x
    · subst hax; simp only [if_true] at this; simp; omega
    · simp only [if_neg hax] at this
      have : (x == a) = false := by simp [Ne.symm hax]
      simp [this]; omega

theorem rr_l1_foldl_update (l : List N) (i : N) (l' : List G) (hi : ∀ x ∈ l, x ≠ i) :
    ∀ st : (N → Finset G) × Finset G,
      l.foldl (fun st a => picking_turn (Function.update L i l' a) a st) st =
        l.foldl (fun st a => picking_turn (L a) a st) st := by
  induction l with
  | nil => intro st; rfl
  | cons x l ih =>
    intro st
    simp only [List.foldl_cons]
    rw [Function.update_of_ne (hi x List.mem_cons_self)]
    exact ih (fun y hy => hi y (List.mem_cons_of_mem _ hy)) _

end rr_l1

theorem rr_l1_seq_getElem (n m : ℕ) [NeZero n] (t : ℕ) (h : t < (round_robin_sequence n m).length) :
    ((round_robin_sequence n m)[t]).val = t % n := by
  simp [round_robin_sequence]

theorem rr_l1_seq_length (n m : ℕ) [NeZero n] : (round_robin_sequence n m).length = m := by
  simp [round_robin_sequence]

theorem rr_l1_count_take_le_one (n m : ℕ) [NeZero n] (k : ℕ) (hk : k ≤ n) (a : Fin n) :
    ((round_robin_sequence n m).take k).count a ≤ 1 := by
  apply List.nodup_iff_count_le_one.mp
  rw [List.nodup_iff_injective_getElem]
  intro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  simp only [List.length_take, rr_l1_seq_length] at hx hy
  have h1 := congrArg Fin.val hxy
  simp only [List.getElem_take, rr_l1_seq_getElem] at h1
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h1
  exact Fin.ext h1

theorem rr_l1_count_drop_le_one (n m : ℕ) [NeZero n] (hm : m ≤ 2 * n) (a : Fin n) :
    ((round_robin_sequence n m).drop n).count a ≤ 1 := by
  apply List.nodup_iff_count_le_one.mp
  rw [List.nodup_iff_injective_getElem]
  intro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  simp only [List.length_drop, rr_l1_seq_length] at hx hy
  have h1 := congrArg Fin.val hxy
  simp only [List.getElem_drop, rr_l1_seq_getElem] at h1
  have e1 : (n + x) % n = x := by rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have e2 : (n + y) % n = y := by rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  rw [e1, e2] at h1
  exact Fin.ext h1

theorem round_robin_pne_ef1_of_card_le_two_mul (n m : ℕ) [NeZero n] (hm : m ≤ 2 * n)
    (w : Fin n → Fin m → ℝ) (hw : ∀ i g, 0 ≤ w i g) (rank : Fin n → Fin m ≃ Fin m)
    (h : is_picking_sequence_pne
      (SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation ⟨w⟩)
      (round_robin_sequence n m) rank) :
    SocialChoice.FairDivision.Indivisible.IsEF1
      (SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation ⟨w⟩)
      (picking_sequence_outcome (round_robin_sequence n m) rank) := by
  intro i j hij hne
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
  have hcount2 : seq.count j ≤ 2 := by
    rw [← List.take_append_drop n seq, List.count_append]
    have h1 := rr_l1_count_take_le_one n m n le_rfl j
    have h2 := rr_l1_count_drop_le_one n m hm j
    rw [← hseq] at h1 h2
    omega
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
