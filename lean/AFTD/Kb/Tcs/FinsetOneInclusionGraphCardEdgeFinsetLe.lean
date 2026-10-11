import AFTD.Prelude
import AFTD.Kb.Tcs.FinsetOneInclusionGraph
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# finset_one_inclusion_graph_card_edgeFinset_le

Topic: combinatorics   Node: fb3c5949070c

Provenance: formalization of a published result. Source: arXiv:2610.08151 (Polynomial-in-r bounds for forbidden traces of uniform hypergraphs), Lemma 2 (one-inclusion graph edge bound). The edge set's Fintype instance is a hypothesis; the count does not depend on it.

If a finite set system F has VC dimension at most d, its one-inclusion graph has at most d·|F| edges.
-/

/-- Ordered pairs of members of `𝒜` whose symmetric difference has exactly one element. -/
def finset_one_inclusion_pairs {α : Type*} [DecidableEq α] (𝒜 : Finset (Finset α)) :
    Finset (Finset α × Finset α) :=
  (𝒜 ×ˢ 𝒜).filter (fun p => (symmDiff p.1 p.2).card = 1)

theorem finset_one_inclusion_pairs_mono {α : Type*} [DecidableEq α] {𝒜 ℬ : Finset (Finset α)}
    (h : 𝒜 ⊆ ℬ) : finset_one_inclusion_pairs 𝒜 ⊆ finset_one_inclusion_pairs ℬ :=
  Finset.filter_subset_filter _ (Finset.product_subset_product h h)

theorem finset_one_inclusion_pairs_inter {α : Type*} [DecidableEq α] (𝒜 ℬ : Finset (Finset α)) :
    finset_one_inclusion_pairs 𝒜 ∩ finset_one_inclusion_pairs ℬ ⊆
      finset_one_inclusion_pairs (𝒜 ∩ ℬ) := by
  intro p hp
  simp only [finset_one_inclusion_pairs, Finset.mem_inter, Finset.mem_filter,
    Finset.mem_product] at hp ⊢
  exact ⟨⟨⟨hp.1.1.1, hp.2.1.1⟩, ⟨hp.1.1.2, hp.2.1.2⟩⟩, hp.1.2⟩

theorem finset_one_inclusion_pairs_card_split {α : Type*} [DecidableEq α] (a : α)
    (𝒜 : Finset (Finset α)) :
    (finset_one_inclusion_pairs 𝒜).card ≤
      (finset_one_inclusion_pairs (𝒜.nonMemberSubfamily a ∪ 𝒜.memberSubfamily a)).card +
      (finset_one_inclusion_pairs (𝒜.nonMemberSubfamily a ∩ 𝒜.memberSubfamily a)).card +
      2 * (𝒜.nonMemberSubfamily a ∩ 𝒜.memberSubfamily a).card := by
  set F0 := 𝒜.nonMemberSubfamily a
  set F1 := 𝒜.memberSubfamily a
  set E := finset_one_inclusion_pairs 𝒜
  set E00 := E.filter (fun p => a ∉ p.1 ∧ a ∉ p.2)
  set E11 := E.filter (fun p => a ∈ p.1 ∧ a ∈ p.2)
  set EX := E.filter (fun p => (a ∈ p.1 ∧ a ∉ p.2) ∨ (a ∉ p.1 ∧ a ∈ p.2))
  have hsplit : E ⊆ E00 ∪ E11 ∪ EX := by
    intro p hp
    simp only [E00, E11, EX, Finset.mem_union, Finset.mem_filter]
    by_cases h1 : a ∈ p.1 <;> by_cases h2 : a ∈ p.2 <;> simp [h1, h2, hp]
  have hcardE : E.card ≤ E00.card + E11.card + EX.card :=
    (Finset.card_le_card hsplit).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  -- E00 sits inside the pairs of F0
  have h00 : E00 ⊆ finset_one_inclusion_pairs F0 := by
    intro p hp
    simp only [E00, E, finset_one_inclusion_pairs, Finset.mem_filter, Finset.mem_product] at hp ⊢
    obtain ⟨⟨⟨hA, hB⟩, hP⟩, ha1, ha2⟩ := hp
    exact ⟨⟨Finset.mem_nonMemberSubfamily.2 ⟨hA, ha1⟩, Finset.mem_nonMemberSubfamily.2 ⟨hB, ha2⟩⟩, hP⟩
  -- E11 injects into the pairs of F1 by erasing `a`
  have h11 : E11.card ≤ (finset_one_inclusion_pairs F1).card := by
    refine Finset.card_le_card_of_injOn (fun p => (p.1.erase a, p.2.erase a)) ?_ ?_
    · intro p hp
      simp only [Finset.mem_coe, E11, E, finset_one_inclusion_pairs, Finset.mem_filter,
        Finset.mem_product] at hp ⊢
      obtain ⟨⟨⟨hA, hB⟩, hP⟩, ha1, ha2⟩ := hp
      refine ⟨⟨Finset.mem_memberSubfamily.2 ⟨by rwa [Finset.insert_erase ha1], by simp⟩,
        Finset.mem_memberSubfamily.2 ⟨by rwa [Finset.insert_erase ha2], by simp⟩⟩, ?_⟩
      have : symmDiff (p.1.erase a) (p.2.erase a) = symmDiff p.1 p.2 := by
        ext x
        by_cases hx : x = a
        · subst hx; simp [Finset.mem_symmDiff, ha1, ha2]
        · simp [Finset.mem_symmDiff, Finset.mem_erase, hx]
      rw [this]; exact hP
    · intro p hp q hq hpq
      simp only [Finset.mem_coe, E11, Finset.mem_filter] at hp hq
      simp only [Prod.mk.injEq] at hpq
      have e1 : p.1 = q.1 := by
        rw [← Finset.insert_erase hp.2.1, ← Finset.insert_erase hq.2.1, hpq.1]
      have e2 : p.2 = q.2 := by
        rw [← Finset.insert_erase hp.2.2, ← Finset.insert_erase hq.2.2, hpq.2]
      exact Prod.ext e1 e2
  -- pairs differing exactly in `a`
  have hX : EX.card ≤ 2 * (F0 ∩ F1).card := by
    have hsd : ∀ p ∈ EX, symmDiff p.1 p.2 = {a} := by
      intro p hp
      simp only [EX, E, finset_one_inclusion_pairs, Finset.mem_filter] at hp
      obtain ⟨⟨-, hP⟩, hx⟩ := hp
      obtain ⟨x, hx1⟩ := Finset.card_eq_one.1 hP
      have : a ∈ symmDiff p.1 p.2 := by
        rw [Finset.mem_symmDiff]; tauto
      rw [hx1, Finset.mem_singleton] at this
      rw [hx1, this]
    have hcard2 : (F0 ∩ F1).card * 2 = ((F0 ∩ F1) ×ˢ (Finset.univ : Finset Bool)).card := by
      rw [Finset.card_product, Finset.card_univ, Fintype.card_bool]
    rw [mul_comm, hcard2]
    refine Finset.card_le_card_of_injOn (fun p => (p.1.erase a, decide (a ∈ p.1))) ?_ ?_
    · intro p hp
      have hs := hsd p hp
      simp only [Finset.mem_coe, EX, E, finset_one_inclusion_pairs, Finset.mem_filter,
        Finset.mem_product] at hp
      obtain ⟨⟨⟨hA, hB⟩, -⟩, hx⟩ := hp
      have hiff : ∀ x, x ≠ a → (x ∈ p.1 ↔ x ∈ p.2) := by
        intro x hxa
        have : x ∉ symmDiff p.1 p.2 := by rw [hs]; simpa using hxa
        rw [Finset.mem_symmDiff] at this
        tauto
      simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_univ, and_true, Finset.mem_inter,
        Finset.mem_nonMemberSubfamily, Finset.mem_memberSubfamily, F0, F1]
      rcases hx with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩
      · have hBe : p.1.erase a = p.2 := by
          ext x
          by_cases hxa : x = a
          · subst hxa; simp [ha2]
          · rw [Finset.mem_erase]; exact ⟨fun h => (hiff x hxa).1 h.2, fun h => ⟨hxa, (hiff x hxa).2 h⟩⟩
        refine ⟨⟨by rw [hBe]; exact hB, by simp⟩, by rwa [Finset.insert_erase ha1], by simp⟩
      · have hAe : p.1.erase a = p.1 := Finset.erase_eq_of_notMem ha1
        have hBi : insert a p.1 = p.2 := by
          ext x
          by_cases hxa : x = a
          · subst hxa; simp [ha2]
          · rw [Finset.mem_insert]; exact ⟨fun h => h.elim (fun e => absurd e hxa) (hiff x hxa).1,
              fun h => Or.inr ((hiff x hxa).2 h)⟩
        rw [hAe]
        exact ⟨⟨hA, ha1⟩, by rw [hBi]; exact hB, ha1⟩
    · intro p hp q hq hpq
      have hsp := hsd p hp
      have hsq := hsd q hq
      simp only [Prod.mk.injEq, decide_eq_decide] at hpq
      obtain ⟨he, hm⟩ := hpq
      have e1 : p.1 = q.1 := by
        by_cases ha : a ∈ p.1
        · rw [← Finset.insert_erase ha, ← Finset.insert_erase (hm.1 ha), he]
        · rw [← Finset.erase_eq_of_notMem ha, ← Finset.erase_eq_of_notMem (fun h => ha (hm.2 h)), he]
      have e2 : p.2 = q.2 := by
        have h1 : p.2 = symmDiff p.1 {a} := by rw [← hsp, symmDiff_symmDiff_cancel_left]
        have h2 : q.2 = symmDiff q.1 {a} := by rw [← hsq, symmDiff_symmDiff_cancel_left]
        rw [h1, h2, e1]
      exact Prod.ext e1 e2
  -- pairs of F0 and F1 against those of the union and the intersection
  have hUI : (finset_one_inclusion_pairs F0).card + (finset_one_inclusion_pairs F1).card ≤
      (finset_one_inclusion_pairs (F0 ∪ F1)).card + (finset_one_inclusion_pairs (F0 ∩ F1)).card := by
    rw [← Finset.card_union_add_card_inter]
    exact Nat.add_le_add
      (Finset.card_le_card (Finset.union_subset
        (finset_one_inclusion_pairs_mono Finset.subset_union_left)
        (finset_one_inclusion_pairs_mono Finset.subset_union_right)))
      (Finset.card_le_card (finset_one_inclusion_pairs_inter F0 F1))
  have := Finset.card_le_card h00
  omega

theorem finset_one_inclusion_pairs_card_le {α : Type*} [DecidableEq α] (u : Finset α) :
    ∀ 𝒜 : Finset (Finset α), (∀ s ∈ 𝒜, s ⊆ u) → ∀ d : ℕ, 𝒜.vcDim ≤ d →
      (finset_one_inclusion_pairs 𝒜).card ≤ 2 * (d * 𝒜.card) := by
  induction u using Finset.induction with
  | empty =>
    intro 𝒜 h𝒜 d _
    have : (finset_one_inclusion_pairs 𝒜).card = 0 := by
      rw [Finset.card_eq_zero, finset_one_inclusion_pairs, Finset.filter_eq_empty_iff]
      intro p hp
      rw [Finset.mem_product] at hp
      rw [Finset.subset_empty.1 (h𝒜 _ hp.1), Finset.subset_empty.1 (h𝒜 _ hp.2)]
      simp
    omega
  | insert a u hau ih =>
    intro 𝒜 h𝒜 d hd
    set F0 := 𝒜.nonMemberSubfamily a
    set F1 := 𝒜.memberSubfamily a
    have hF0 : ∀ s ∈ F0, s ⊆ u := by
      intro s hs
      rw [Finset.mem_nonMemberSubfamily] at hs
      exact (Finset.subset_insert_iff_of_notMem hs.2).1 (h𝒜 s hs.1)
    have hF1 : ∀ s ∈ F1, s ⊆ u := by
      intro s hs
      rw [Finset.mem_memberSubfamily] at hs
      exact (Finset.subset_insert_iff_of_notMem hs.2).1
        ((Finset.subset_insert _ _).trans (h𝒜 _ hs.1))
    have hU : ∀ s ∈ F0 ∪ F1, s ⊆ u := by
      intro s hs
      rcases Finset.mem_union.1 hs with h | h
      exacts [hF0 s h, hF1 s h]
    have hI : ∀ s ∈ F0 ∩ F1, s ⊆ u := fun s hs => hF0 s (Finset.mem_inter.1 hs).1
    have notmem : ∀ ℬ : Finset (Finset α), (∀ s ∈ ℬ, s ⊆ u) → ∀ s, ℬ.Shatters s → a ∉ s := by
      intro ℬ hℬ s hs ha
      obtain ⟨v, hv, hsv⟩ := hs.exists_superset
      exact hau (hℬ v hv (hsv ha))
    have shU : ∀ s, (F0 ∪ F1).Shatters s → 𝒜.Shatters s := by
      intro s hs t ht
      have has := notmem _ hU s hs
      obtain ⟨w, hw, hsw⟩ := hs ht
      rcases Finset.mem_union.1 hw with hw | hw
      · rw [Finset.mem_nonMemberSubfamily] at hw
        exact ⟨w, hw.1, hsw⟩
      · rw [Finset.mem_memberSubfamily] at hw
        exact ⟨insert a w, hw.1, by rw [Finset.inter_insert_of_notMem has, hsw]⟩
    have shI : ∀ s, (F0 ∩ F1).Shatters s → 𝒜.Shatters (insert a s) := by
      intro s hs t ht
      have has := notmem _ hI s hs
      by_cases hat : a ∈ t
      · have hsub : t.erase a ⊆ s := by
          intro x hx
          rw [Finset.mem_erase] at hx
          have := ht hx.2
          rw [Finset.mem_insert] at this
          exact this.resolve_left hx.1
        obtain ⟨w, hw, hsw⟩ := hs hsub
        have hw1 := (Finset.mem_inter.1 hw).2
        rw [Finset.mem_memberSubfamily] at hw1
        refine ⟨insert a w, hw1.1, ?_⟩
        rw [← Finset.insert_inter_distrib, hsw, Finset.insert_erase hat]
      · have hsub : t ⊆ s := by
          intro x hx
          have := ht hx
          rw [Finset.mem_insert] at this
          exact this.resolve_left (fun e => hat (e ▸ hx))
        obtain ⟨w, hw, hsw⟩ := hs hsub
        have hw0 := (Finset.mem_inter.1 hw).1
        rw [Finset.mem_nonMemberSubfamily] at hw0
        refine ⟨w, hw0.1, ?_⟩
        rw [Finset.insert_inter_of_notMem hw0.2, hsw]
    have vcU : (F0 ∪ F1).vcDim ≤ d := by
      unfold Finset.vcDim
      refine Finset.sup_le fun s hs => ?_
      exact ((shU s (Finset.mem_shatterer.1 hs)).card_le_vcDim).trans hd
    have vcI : (F0 ∩ F1).vcDim ≤ d - 1 := by
      unfold Finset.vcDim
      refine Finset.sup_le fun s hs => ?_
      have hs' := Finset.mem_shatterer.1 hs
      have h1 := (shI s hs').card_le_vcDim
      rw [Finset.card_insert_of_notMem (notmem _ hI s hs')] at h1
      omega
    have hIempty : d = 0 → F0 ∩ F1 = ∅ := by
      intro hd0
      by_contra hne
      have h1 := (shI ∅ (Finset.shatters_empty.2 (Finset.nonempty_iff_ne_empty.2 hne))).card_le_vcDim
      simp only [insert_empty_eq, Finset.card_singleton] at h1
      omega
    have ihU := ih (F0 ∪ F1) hU d vcU
    have ihI := ih (F0 ∩ F1) hI (d - 1) vcI
    have hcard : 𝒜.card = (F0 ∪ F1).card + (F0 ∩ F1).card := by
      rw [Finset.card_union_add_card_inter, add_comm,
        Finset.card_memberSubfamily_add_card_nonMemberSubfamily]
    have hedge : (finset_one_inclusion_pairs 𝒜).card ≤
        (finset_one_inclusion_pairs (F0 ∪ F1)).card + (finset_one_inclusion_pairs (F0 ∩ F1)).card +
          2 * (F0 ∩ F1).card :=
      finset_one_inclusion_pairs_card_split a 𝒜
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · have hI0 := hIempty hd0
      subst hd0
      rw [hI0] at hedge
      have h0 : (finset_one_inclusion_pairs (∅ : Finset (Finset α))).card = 0 := by
        simp [finset_one_inclusion_pairs]
      rw [h0, Finset.card_empty] at hedge
      simp only [zero_mul, mul_zero] at ihU ⊢
      omega
    · have h1 : d * 𝒜.card = d * (F0 ∪ F1).card + d * (F0 ∩ F1).card := by
        rw [hcard, mul_add]
      have h2 : (d - 1) * (F0 ∩ F1).card + (F0 ∩ F1).card = d * (F0 ∩ F1).card := by
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hdpos
        simp only [Nat.zero_add, Nat.add_sub_cancel]
        ring
      linarith

theorem finset_one_inclusion_graph_card_edgeFinset_le {α : Type*} [DecidableEq α]
    (𝓕 : Finset (Finset α)) [Fintype (finset_one_inclusion_graph 𝓕).edgeSet] (d : ℕ)
    (hd : 𝓕.vcDim ≤ d) :
    (finset_one_inclusion_graph 𝓕).edgeFinset.card ≤ d * 𝓕.card := by
  classical
  have hpairs := finset_one_inclusion_pairs_card_le (𝓕.sup id) 𝓕
    (fun s hs => Finset.le_sup (f := id) hs) d hd
  have hbij : ((Finset.univ : Finset (𝓕 × 𝓕)).filter
      (fun x => (finset_one_inclusion_graph 𝓕).Adj x.1 x.2)).card =
        (finset_one_inclusion_pairs 𝓕).card := by
    apply Finset.card_bij (fun x _ => ((x.1 : Finset α), (x.2 : Finset α)))
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [finset_one_inclusion_pairs, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨x.1.2, x.2.2⟩, hx⟩
    · intro x _ y _ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)
    · intro b hb
      simp only [finset_one_inclusion_pairs, Finset.mem_filter, Finset.mem_product] at hb
      refine ⟨(⟨b.1, hb.1.1⟩, ⟨b.2, hb.1.2⟩), ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hb.2
  have key : 2 * (finset_one_inclusion_graph 𝓕).edgeFinset.card =
      (finset_one_inclusion_pairs 𝓕).card := by
    rw [← hbij]
    convert SimpleGraph.two_mul_card_edgeFinset (finset_one_inclusion_graph 𝓕)
  have h2 : 2 * (finset_one_inclusion_graph 𝓕).edgeFinset.card ≤ 2 * (d * 𝓕.card) := by
    rw [key]; exact hpairs
  exact Nat.le_of_mul_le_mul_left h2 (by norm_num)
