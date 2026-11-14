import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphDirectedCycleOn
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# digraph_general_robust_two_cycle_free_cut

Topic: graphs   Node: 7aa6af3aa345

Provenance: helper lemma. General form of the robust two-cycle cut-layer argument for OP-110; experiment 26331 checks the finite layer optimization for d through 24.

Assuming the displayed robust two-cycle criterion, every two-cycle-free part of size at least d in a graph with outdegree at least d on the part has at least choose(d,2)−1 outgoing arcs, for d≥3.
-/

lemma digraph_general_robust_two_cycle_free_cut_aux_partition_card
    {α : Type} [Fintype α] [DecidableEq α] (B : Finset α) (p : α → Prop) [DecidablePred p] :
    (Finset.univ.filter p).card = (B.filter p).card + (Bᶜ.filter p).card := by
  classical
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext x; simp [Finset.mem_filter]; tauto
  · rw [Finset.disjoint_left]
    intro x hx hy
    simp only [Finset.mem_filter, Finset.mem_compl] at hx hy
    exact hy.1 hx.1

lemma digraph_general_robust_two_cycle_free_cut_aux_filter_sdiff
    {α : Type} [DecidableEq α] (B S : Finset α) (p : α → Prop) [DecidablePred p] :
    (B \ S).filter p = (B.filter p) \ (S.filter p) := by
  classical
  ext x
  simp only [Finset.mem_filter, Finset.mem_sdiff]
  tauto

lemma digraph_general_robust_two_cycle_free_cut_aux_card_sdiff_filter
    {α : Type} [DecidableEq α] (B S : Finset α) (p : α → Prop) [DecidablePred p] (hSB : S ⊆ B) :
    ((B \ S).filter p).card = (B.filter p).card - (S.filter p).card := by
  classical
  rw [digraph_general_robust_two_cycle_free_cut_aux_filter_sdiff]
  have hsub : S.filter p ⊆ B.filter p := by
    intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨hSB hx.1, hx.2⟩
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub]

lemma digraph_general_robust_two_cycle_free_cut_aux_threshold
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (d : ℕ) (hd : 3 ≤ d) (B : Finset α) (hB : d ≤ B.card)
    (hdeg : ∀ v ∈ B, d ≤ (Finset.univ.filter fun w => D.Adj v w).card)
    (hrobust : ∀ T : Finset α, T.Nonempty →
      (∀ v ∈ T, 2 ≤ (T.filter fun w => D.Adj v w).card) →
      (T.filter fun v => (T.filter fun w => D.Adj v w).card < 3).card ≤ 2 →
      ∃ c : Fin 2 → Finset α, (∀ i, c i ⊆ T ∧ digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j)))
    (hno : ¬ ∃ c : Fin 2 → Finset α, (∀ i, c i ⊆ B ∧ digraph_directed_cycle_on D (c i)) ∧
      Pairwise (fun i j => Disjoint (c i) (c j)))
    (j : ℕ) (hj1 : 1 ≤ j) (hj2 : j ≤ d - 2) :
    d - 1 - j ≤ (B.filter fun v => j + 1 ≤ (Bᶜ.filter fun w => D.Adj v w).card).card ∨
    d + 1 - j ≤ (B.filter fun v => j ≤ (Bᶜ.filter fun w => D.Adj v w).card).card := by
  classical
  set a : α → ℕ := fun v => (Bᶜ.filter fun w => D.Adj v w).card with ha
  set S : Finset α := B.filter (fun v => j + 1 ≤ a v) with hS
  have hSB : S ⊆ B := Finset.filter_subset _ _
  by_cases hSc : d - 1 - j ≤ S.card
  · exact Or.inl hSc
  · right
    have hScard_le : S.card ≤ d - 2 - j := by omega
    have hTS : B \ S ⊆ B := Finset.sdiff_subset
    have hTcard : j + 2 ≤ (B \ S).card := by
      have h := Finset.card_sdiff_add_card_eq_card hSB
      omega
    have hTne : (B \ S).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro h
      rw [h] at hTcard
      simp at hTcard
    have hsplit : ∀ v, (Finset.univ.filter fun w => D.Adj v w).card
        = (B.filter fun w => D.Adj v w).card + a v := by
      intro v
      have h := digraph_general_robust_two_cycle_free_cut_aux_partition_card B (fun w => D.Adj v w)
      have hav : a v = (Bᶜ.filter fun w => D.Adj v w).card := rfl
      omega
    have hmin : ∀ v ∈ B \ S, 2 ≤ ((B \ S).filter fun w => D.Adj v w).card := by
      intro v hv
      have hvB : v ∈ B := hTS hv
      have hvS : v ∉ S := (Finset.mem_sdiff.mp hv).2
      have hav : a v ≤ j := by
        by_contra h
        exact hvS (Finset.mem_filter.mpr ⟨hvB, by omega⟩)
      have hsp := hsplit v
      have hdegv := hdeg v hvB
      have hcard := digraph_general_robust_two_cycle_free_cut_aux_card_sdiff_filter B S (fun w => D.Adj v w) hSB
      have hSf : (S.filter fun w => D.Adj v w).card ≤ S.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      omega
    have hcnt3 : 3 ≤ ((B \ S).filter fun v => ((B \ S).filter fun w => D.Adj v w).card < 3).card := by
      by_contra h
      push_neg at h
      have h2 : ((B \ S).filter fun v => ((B \ S).filter fun w => D.Adj v w).card < 3).card ≤ 2 := by omega
      obtain ⟨c, hc⟩ := hrobust (B \ S) hTne hmin h2
      exact hno ⟨c, fun i => ⟨Finset.Subset.trans (hc.1 i).1 hTS, (hc.1 i).2⟩, hc.2⟩
    have hsmall : ∀ v ∈ (B \ S).filter (fun v => ((B \ S).filter fun w => D.Adj v w).card < 3),
        a v ≤ j ∧ d - j ≤ (B.filter fun w => D.Adj v w).card
          ∧ (B.filter fun w => D.Adj v w).card ≤ 2 + S.card := by
      intro v hv
      obtain ⟨hvT, hlt⟩ := Finset.mem_filter.mp hv
      have hvB : v ∈ B := hTS hvT
      have hvS : v ∉ S := (Finset.mem_sdiff.mp hvT).2
      have hav : a v ≤ j := by
        by_contra h
        exact hvS (Finset.mem_filter.mpr ⟨hvB, by omega⟩)
      have hsp := hsplit v
      have hdegv := hdeg v hvB
      have hcard := digraph_general_robust_two_cycle_free_cut_aux_card_sdiff_filter B S (fun w => D.Adj v w) hSB
      have hSf : (S.filter fun w => D.Adj v w).card ≤ S.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      exact ⟨hav, by omega, by omega⟩
    have hSge : d - 2 - j ≤ S.card := by
      obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < ((B \ S).filter fun v => ((B \ S).filter fun w => D.Adj v w).card < 3).card)
      have := (hsmall v hv).2.1
      have := (hsmall v hv).2.2
      omega
    have hSeq : S.card = d - 2 - j := by omega
    have hkey : ∀ v ∈ (B \ S).filter (fun v => ((B \ S).filter fun w => D.Adj v w).card < 3), a v = j := by
      intro v hv
      obtain ⟨hvT, hlt⟩ := Finset.mem_filter.mp hv
      obtain ⟨hav, hlow, hup⟩ := hsmall v hv
      have hvB : v ∈ B := hTS hvT
      have hsp := hsplit v
      have hdegv := hdeg v hvB
      have hb : (B.filter fun w => D.Adj v w).card = d - j := by omega
      omega
    have hnj : d + 1 - j ≤ (B.filter fun v => j ≤ a v).card := by
      have hSsub : S ⊆ B.filter (fun v => j ≤ a v) := by
        intro v hv
        have hh : v ∈ B ∧ j + 1 ≤ a v := Finset.mem_filter.mp hv
        exact Finset.mem_filter.mpr ⟨hh.1, by omega⟩
      have hXsub : (B \ S).filter (fun v => ((B \ S).filter fun w => D.Adj v w).card < 3)
          ⊆ B.filter (fun v => j ≤ a v) := by
        intro v hv
        have hvT : v ∈ B \ S := (Finset.mem_filter.mp hv).1
        have hone : a v = j := hkey v hv
        exact Finset.mem_filter.mpr ⟨hTS hvT, by omega⟩
      have hdisj : Disjoint S ((B \ S).filter (fun v => ((B \ S).filter fun w => D.Adj v w).card < 3)) := by
        rw [Finset.disjoint_left]
        intro v hvS hvX
        have hvT : v ∈ B \ S := (Finset.mem_filter.mp hvX).1
        exact (Finset.mem_sdiff.mp hvT).2 hvS
      have hunion : (S ∪ (B \ S).filter (fun v => ((B \ S).filter fun w => D.Adj v w).card < 3)).card
          = S.card + ((B \ S).filter fun v => ((B \ S).filter fun w => D.Adj v w).card < 3).card :=
        Finset.card_union_of_disjoint hdisj
      have hle : (S ∪ (B \ S).filter (fun v => ((B \ S).filter fun w => D.Adj v w).card < 3)).card
          ≤ (B.filter fun v => j ≤ a v).card :=
        Finset.card_le_card (Finset.union_subset hSsub hXsub)
      omega
    exact hnj

lemma digraph_general_robust_two_cycle_free_cut_aux_layer_cake
    {α : Type} [Fintype α] [DecidableEq α] (B : Finset α) (a : α → ℕ) (M : ℕ) :
    ∑ k ∈ Finset.range M, (B.filter fun v => k+1 ≤ a v).card ≤ ∑ v ∈ B, a v := by
  classical
  have h1 : ∀ k, (B.filter fun v => k+1 ≤ a v).card = ∑ v ∈ B, (if k+1 ≤ a v then 1 else 0) := by
    intro k; rw [Finset.card_filter]
  simp only [h1]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro v hv
  have h2 : ∑ k ∈ Finset.range M, (if k+1 ≤ a v then 1 else 0)
      = ∑ k ∈ (Finset.range M).filter (fun k => k+1 ≤ a v), (1:ℕ) := by
    rw [Finset.sum_filter]
  rw [h2]
  have h3 : ((Finset.range M).filter (fun k => k+1 ≤ a v)).card * 1
      = ∑ k ∈ (Finset.range M).filter (fun k => k+1 ≤ a v), (1:ℕ) := by
    rw [Finset.sum_const_nat]; intro x hx; rfl
  rw [← h3]
  have hsub : (Finset.range M).filter (fun k => k+1 ≤ a v) ⊆ Finset.range (a v) := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
    omega
  have := Finset.card_le_card hsub
  simp only [Finset.card_range] at this
  omega

lemma digraph_general_robust_two_cycle_free_cut_aux_sum_cast_double (m : ℕ) :
    (2 : ℤ) * ∑ k ∈ Finset.range m, (k : ℤ) = (m : ℤ) * ((m : ℤ) - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    push_cast
    nlinarith [ih]

lemma digraph_general_robust_two_cycle_free_cut_aux_arith
    (d : ℕ) (hd : 3 ≤ d) (n : ℕ → ℕ)
    (hmono : ∀ i j : ℕ, i ≤ j → n j ≤ n i)
    (halt : ∀ j : ℕ, 1 ≤ j → j ≤ d - 2 →
      d - 1 - j ≤ n (j + 1) ∨ d + 1 - j ≤ n j) :
    Nat.choose d 2 - 1 ≤ ∑ k ∈ Finset.range (d - 1), n (k + 1) := by
  classical
  have hdm : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega : (1:ℕ) ≤ d)]; try norm_num
  set E : ℕ → ℤ := fun k => (n (k + 1) : ℤ) + (k : ℤ) - ((d : ℤ) - 1) with hE
  have hE1 : ∀ k ∈ Finset.range (d - 1), -1 ≤ E k := by
    intro k hk
    rw [Finset.mem_range] at hk
    rcases Nat.lt_or_ge k (d - 2) with hlt | hge
    · have hk3 : k ≤ d - 3 := by omega
      by_contra hcon
      push_neg at hcon
      have hA : (n (k+1) : ℤ) + (k:ℤ) ≤ (d:ℤ) - 3 := by
        simp only [hE] at hcon; push_cast at hcon ⊢; linarith
      have hAn : n (k+1) + k ≤ d - 3 := by
        have h3 : ((d - 3 : ℕ) : ℤ) = (d:ℤ) - 3 := by
          rw [Nat.cast_sub (by omega : (3:ℕ) ≤ d)]; try norm_num
        have : ((n (k+1) + k : ℕ) : ℤ) ≤ ((d - 3 : ℕ) : ℤ) := by push_cast; linarith
        exact_mod_cast this
      have hnot2 : ¬ (d + 1 - (k+1) ≤ n (k+1)) := by
        intro h; omega
      have h1 : 1 ≤ k+1 := by omega
      have h2 : k+1 ≤ d-2 := by omega
      rcases halt (k+1) h1 h2 with h | h
      · have hd1 : d ≤ n (k+1+1) + (k+2) := by omega
        have hE0 : 0 ≤ E (k+1) := by
          simp only [hE]
          have hcast : (d:ℤ) ≤ (n (k+1+1) : ℤ) + ((k+2 : ℕ) : ℤ) := by exact_mod_cast hd1
          push_cast at hcast ⊢
          linarith
        have hm := hmono (k+1) (k+1+1) (by omega)
        have hcast2 : (n (k+1+1) : ℤ) ≤ (n (k+1) : ℤ) := by exact_mod_cast hm
        have hEle : E (k+1) ≤ -1 := by
          simp only [hE]; push_cast; linarith
        linarith
      · exact absurd h hnot2
    · have hkc : (k : ℤ) = (d : ℤ) - 2 := by
        rw [show k = d - 2 by omega, Nat.cast_sub (by omega : (2:ℕ) ≤ d)]; try norm_num
      simp only [hE]
      have hpos : (0:ℤ) ≤ (n (k+1) : ℤ) := by positivity
      linarith
  have hMP : (Finset.range (d-1)).filter (fun k => E k = -1) ⊆
      ((Finset.range (d-1)).filter (fun k => 1 ≤ E k)).image (fun k => k + 1) ∪ {0} := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_image,
      Finset.mem_singleton] at hk ⊢
    obtain ⟨hklt, hkE⟩ := hk
    by_cases hk0 : k = 0
    · exact Or.inr hk0
    · left
      have hk1 : 1 ≤ k := by omega
      have hk2 : k ≤ d - 2 := by omega
      rcases halt k hk1 hk2 with h | h
      · exfalso
        have hE0 : 0 ≤ E k := by
          simp only [hE]
          have hcast : ((d - 1 - k : ℕ) : ℤ) = (d:ℤ) - 1 - (k:ℤ) := by
            rw [Nat.cast_sub (by omega : k ≤ d - 1), hdm]; try norm_num
          have hle : ((d - 1 - k : ℕ) : ℤ) ≤ (n (k+1) : ℤ) := by exact_mod_cast h
          push_cast
          linarith
        linarith
      · refine ⟨k - 1, ⟨by omega, ?_⟩, by omega⟩
        have hkk : k - 1 + 1 = k := by omega
        have hcast : ((d + 1 - k : ℕ) : ℤ) = (d:ℤ) + 1 - (k:ℤ) := by
          rw [Nat.cast_sub (by omega : k ≤ d + 1)]; push_cast; try ring
        have hle : ((d + 1 - k : ℕ) : ℤ) ≤ (n k : ℤ) := by exact_mod_cast h
        simp only [hE, hkk]
        push_cast
        linarith
  have hsumE : (-1 : ℤ) ≤ ∑ k ∈ Finset.range (d - 1), E k := by
    set S := Finset.range (d - 1) with hS
    set M := S.filter (fun k => E k = -1) with hM
    set P := S.filter (fun k => 1 ≤ E k) with hP
    have hMS : M ⊆ S := Finset.filter_subset _ _
    have hPS : P ⊆ S := Finset.filter_subset _ _
    have hPM : P ⊆ S \ M := by
      intro x hx
      obtain ⟨hxS, hxE⟩ := Finset.mem_filter.mp hx
      exact Finset.mem_sdiff.mpr ⟨hxS, by intro h; rw [Finset.mem_filter] at h; linarith [h.2]⟩
    have hM0 : ∑ k ∈ M, (E k + 1) = 0 := by
      rw [Finset.sum_eq_zero]
      intro k hk
      have := (Finset.mem_filter.mp hk).2
      linarith
    have hsplit : ∑ k ∈ S, (E k + 1) = ∑ k ∈ M, (E k + 1) + ∑ k ∈ S \ M, (E k + 1) := by
      have := Finset.sum_sdiff hMS (f := fun k => E k + 1)
      linarith [this]
    have hpt : ∀ k ∈ S \ M, (1:ℤ) + (if k ∈ P then 1 else 0) ≤ E k + 1 := by
      intro k hk
      obtain ⟨hkS, hkM⟩ := Finset.mem_sdiff.mp hk
      by_cases hkP : k ∈ P
      · simp only [if_pos hkP]
        have := (Finset.mem_filter.mp hkP).2
        linarith
      · simp only [if_neg hkP]
        have h1 := hE1 k hkS
        have hne : E k ≠ -1 := by intro h; exact hkM (Finset.mem_filter.mpr ⟨hkS, h⟩)
        omega
    have hrest : ((S \ M).card : ℤ) + (P.card : ℤ) ≤ ∑ k ∈ S \ M, (E k + 1) := by
      have hle := Finset.sum_le_sum hpt
      have heq1 : ∑ k ∈ S \ M, ((1:ℤ) + (if k ∈ P then 1 else 0))
          = ((S \ M).card : ℤ) + ∑ k ∈ S \ M, (if k ∈ P then (1:ℤ) else 0) := by
        rw [Finset.sum_add_distrib]
        simp
      have heq2 : ∑ k ∈ S \ M, (if k ∈ P then (1:ℤ) else 0) = (P.card : ℤ) := by
        rw [Finset.sum_boole]
        have : (S \ M).filter (fun k => k ∈ P) = P := by
          rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hPM]
        rw [this]
      rw [heq1, heq2] at hle
      exact hle
    have hSMcard : ((S \ M).card : ℤ) = (S.card : ℤ) - (M.card : ℤ) := by
      have h := Finset.card_sdiff_add_card_eq_card hMS
      push_cast [h]; linarith
    have hPle : (P.card : ℤ) - (M.card : ℤ) ≥ -1 := by
      have hm : M ⊆ P.image (fun k => k + 1) ∪ {0} := hMP
      have h1 : M.card ≤ (P.image (fun k => k + 1) ∪ {0}).card := Finset.card_le_card hm
      have h2 : (P.image (fun k => k + 1) ∪ {0}).card ≤ P.card + 1 := by
        have h4 := Finset.card_union_le (P.image (fun k => k + 1)) ({0} : Finset ℕ)
        have h3 : (P.image (fun k => k + 1)).card ≤ P.card := Finset.card_image_le
        simp only [Finset.card_singleton] at h4 ⊢
        omega
      omega
    have hSsum : (S.card : ℤ) = (M.card : ℤ) + ((S \ M).card : ℤ) := by
      rw [hSMcard]; ring
    have hES : ∑ k ∈ S, E k = ∑ k ∈ S, (E k + 1) - (S.card : ℤ) := by
      rw [Finset.sum_add_distrib]
      simp
    rw [show ∑ k ∈ Finset.range (d-1), E k = ∑ k ∈ S, E k from rfl, hES, hsplit, hM0]
    linarith
  have hEsum : ∑ k ∈ Finset.range (d-1), E k
      = (∑ k ∈ Finset.range (d-1), (n (k+1) : ℤ))
        + (∑ k ∈ Finset.range (d-1), (k:ℤ)) - ((d-1 : ℕ) : ℤ) * ((d:ℤ) - 1) := by
    simp only [hE]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    simp [Finset.card_range]
    try ring
  have hfinal : (d : ℤ) * ((d:ℤ) - 1) - 2 ≤ 2 * ∑ k ∈ Finset.range (d-1), (n (k+1) : ℤ) := by
    have hid := digraph_general_robust_two_cycle_free_cut_aux_sum_cast_double (d-1)
    rw [hdm] at hid
    have hsE := hsumE
    rw [hEsum, hdm] at hsE
    nlinarith [hsE, hid]
  have hnat : d * (d-1) ≤ 2 * (∑ k ∈ Finset.range (d-1), n (k+1) + 1) := by
    have h1' : ((d*(d-1) : ℕ) : ℤ) = (d:ℤ) * ((d:ℤ)-1) := by
      rw [Nat.cast_mul, hdm]; try ring
    have h2' : ((2 * (∑ k ∈ Finset.range (d-1), n (k+1) + 1) : ℕ) : ℤ)
        = 2 * ((∑ k ∈ Finset.range (d-1), (n (k+1) : ℤ)) + 1) := by
      push_cast; try ring
    have : ((d*(d-1) : ℕ) : ℤ) ≤ ((2 * (∑ k ∈ Finset.range (d-1), n (k+1) + 1) : ℕ) : ℤ) := by
      rw [h1', h2']; linarith [hfinal]
    exact_mod_cast this
  have h2 : d * (d - 1) / 2 ≤ ∑ k ∈ Finset.range (d-1), n (k+1) + 1 := by
    rw [Nat.div_le_iff_le_mul (by norm_num : 0 < 2)]
    omega
  rw [Nat.choose_two_right]
  omega

theorem digraph_general_robust_two_cycle_free_cut
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (d : ℕ) (hd : 3 ≤ d) (B : Finset α) (hB : d ≤ B.card)
    (hdeg : ∀ v ∈ B, d ≤ (Finset.univ.filter fun w => D.Adj v w).card)
    (hrobust : ∀ T : Finset α, T.Nonempty →
      (∀ v ∈ T, 2 ≤ (T.filter fun w => D.Adj v w).card) →
      (T.filter fun v => (T.filter fun w => D.Adj v w).card < 3).card ≤ 2 →
      ∃ c : Fin 2 → Finset α, (∀ i, c i ⊆ T ∧ digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j)))
    (hno : ¬ ∃ c : Fin 2 → Finset α, (∀ i, c i ⊆ B ∧ digraph_directed_cycle_on D (c i)) ∧
      Pairwise (fun i j => Disjoint (c i) (c j))) :
    Nat.choose d 2 - 1 ≤ ∑ v ∈ B, (Bᶜ.filter fun w => D.Adj v w).card := by
  classical
  set a : α → ℕ := fun v => (Bᶜ.filter fun w => D.Adj v w).card with ha
  set n : ℕ → ℕ := fun k => (B.filter fun v => k ≤ a v).card with hn
  have hmono : ∀ i j : ℕ, i ≤ j → n j ≤ n i := by
    intro i j hij
    show (B.filter fun v => j ≤ a v).card ≤ (B.filter fun v => i ≤ a v).card
    apply Finset.card_le_card
    intro v hv
    simp only [Finset.mem_filter] at hv ⊢
    exact ⟨hv.1, le_trans hij hv.2⟩
  have hthresh : ∀ j : ℕ, 1 ≤ j → j ≤ d - 2 →
      d - 1 - j ≤ n (j + 1) ∨ d + 1 - j ≤ n j := by
    intro j hj1 hj2
    show d - 1 - j ≤ (B.filter fun v => j + 1 ≤ a v).card ∨
      d + 1 - j ≤ (B.filter fun v => j ≤ a v).card
    exact digraph_general_robust_two_cycle_free_cut_aux_threshold α D d hd B hB hdeg hrobust hno j hj1 hj2
  have harith := digraph_general_robust_two_cycle_free_cut_aux_arith d hd n hmono hthresh
  have hlayer := digraph_general_robust_two_cycle_free_cut_aux_layer_cake B a (d-1)
  have hlayer' : ∑ k ∈ Finset.range (d-1), n (k+1) ≤ ∑ v ∈ B, a v := hlayer
  exact le_trans harith hlayer'
