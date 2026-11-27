import AFTD.Prelude

/-!
# op309_ten_vertex_uniform_p3_host_selection_impossible

Topic: graphs   Node: 00c239a095be

Provenance: helper lemma. OP-309 uniform-host selection analysis; experiments 42443 and 42461.

No ten-vertex cubic graph has a selected P3 forest with independent uncovered vertices, no outside leaf-to-leaf or center-to-center edges, and every uncovered vertex adjacent entirely to leaves or entirely to centers.
-/

open SimpleGraph Finset

private lemma op309_ten_vertex_uniform_p3_host_selection_impossible_edge_endpoints {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (e : G.edgeSet) :
    ∃ u v, G.Adj u v ∧ e.1 = s(u, v) := by
  have key : ∀ x : Sym2 V, x ∈ G.edgeSet → ∃ u v : V, G.Adj u v ∧ x = s(u, v) := by
    intro x hx
    induction x using Sym2.ind with
    | _ u v => exact ⟨u, v, (SimpleGraph.mem_edgeSet G).mp hx, rfl⟩
  exact key e.1 e.2

private lemma op309_ten_vertex_uniform_p3_host_selection_impossible_sel_oriented {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (R : Finset G.edgeSet) (d : V → ℕ)
    (hd : ∀ v, d v = (R.filter fun e => v ∈ e.1).card)
    (hle : ∀ v, d v ≤ 2) (hadj : ∀ u v, G.Adj u v → d u ≠ d v)
    (e : G.edgeSet) (he : e ∈ R) :
    ∃ u v, G.Adj u v ∧ e.1 = s(u, v) ∧ d u = 1 ∧ d v = 2 := by
  classical
  obtain ⟨a, b, hab, heq⟩ := op309_ten_vertex_uniform_p3_host_selection_impossible_edge_endpoints G e
  have hamem : a ∈ e.1 := by rw [heq]; exact Sym2.mem_iff.mpr (Or.inl rfl)
  have hbmem : b ∈ e.1 := by rw [heq]; exact Sym2.mem_iff.mpr (Or.inr rfl)
  have hda1 : 1 ≤ d a := by
    rw [hd a, Finset.one_le_card]; exact ⟨e, by simp [he, hamem]⟩
  have hdb1 : 1 ≤ d b := by
    rw [hd b, Finset.one_le_card]; exact ⟨e, by simp [he, hbmem]⟩
  have hne := hadj a b hab
  have ha2 := hle a; have hb2 := hle b
  have hcases : (d a = 1 ∧ d b = 2) ∨ (d a = 2 ∧ d b = 1) := by omega
  rcases hcases with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact ⟨a, b, hab, heq, ha, hb⟩
  · refine ⟨b, a, (G.adj_comm a b).mp hab, ?_, hb, ha⟩
    rw [heq, Sym2.eq_iff]; exact Or.inr ⟨rfl, rfl⟩

private lemma op309_ten_vertex_uniform_p3_host_selection_impossible_sel_filters {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (R : Finset G.edgeSet) (d : V → ℕ)
    (hd : ∀ v, d v = (R.filter fun e => v ∈ e.1).card)
    (hle : ∀ v, d v ≤ 2) (hadj : ∀ u v, G.Adj u v → d u ≠ d v)
    (e : G.edgeSet) (he : e ∈ R) :
    ((Finset.univ.filter (fun w => d w = 1)).filter (fun w => w ∈ e.1)).card = 1 ∧
    ((Finset.univ.filter (fun w => d w = 2)).filter (fun w => w ∈ e.1)).card = 1 := by
  classical
  obtain ⟨u, v, huv, heq, hdu, hdv⟩ := op309_ten_vertex_uniform_p3_host_selection_impossible_sel_oriented G R d hd hle hadj e he
  constructor
  · have hset : (Finset.univ.filter (fun w => d w = 1)).filter (fun w => w ∈ e.1) = {u} := by
      ext w
      rw [heq]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Sym2.mem_iff, Finset.mem_singleton]
      constructor
      · rintro ⟨hdw, hwu | hwv⟩
        · exact hwu
        · rw [hwv] at hdw; omega
      · rintro rfl; exact ⟨hdu, Or.inl rfl⟩
    rw [hset, Finset.card_singleton]
  · have hset : (Finset.univ.filter (fun w => d w = 2)).filter (fun w => w ∈ e.1) = {v} := by
      ext w
      rw [heq]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Sym2.mem_iff, Finset.mem_singleton]
      constructor
      · rintro ⟨hdw, hwu | hwv⟩
        · rw [hwu] at hdw; omega
        · exact hwv
      · rintro rfl; exact ⟨hdv, Or.inr rfl⟩
    rw [hset, Finset.card_singleton]

private lemma op309_ten_vertex_uniform_p3_host_selection_impossible_sel_double {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (R : Finset G.edgeSet) (S : Finset V) :
    ∑ v ∈ S, (R.filter fun e => v ∈ e.1).card
      = ∑ e ∈ R, (S.filter fun w => w ∈ e.1).card := by
  classical
  calc ∑ v ∈ S, (R.filter fun e => v ∈ e.1).card
      = ∑ v ∈ S, ∑ e ∈ R, (if v ∈ e.1 then 1 else 0) := by
        apply Finset.sum_congr rfl; intro v hv
        rw [Finset.card_filter]
    _ = ∑ e ∈ R, ∑ v ∈ S, (if v ∈ e.1 then 1 else 0) := Finset.sum_comm
    _ = ∑ e ∈ R, (S.filter fun w => w ∈ e.1).card := by
        apply Finset.sum_congr rfl; intro e he
        rw [Finset.card_filter]

private lemma op309_ten_vertex_uniform_p3_host_selection_impossible_sum_nbr_comm {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S TT : Finset V) :
    ∑ v ∈ S, (G.neighborFinset v ∩ TT).card = ∑ w ∈ TT, (G.neighborFinset w ∩ S).card := by
  classical
  have h1 : ∀ v, G.neighborFinset v ∩ TT = TT.filter (fun w => G.Adj v w) := by
    intro v; ext w; simp [mem_neighborFinset, and_comm]
  have h2 : ∀ w, G.neighborFinset w ∩ S = S.filter (fun v => G.Adj w v) := by
    intro w; ext v; simp [mem_neighborFinset, and_comm]
  calc ∑ v ∈ S, (G.neighborFinset v ∩ TT).card
      = ∑ v ∈ S, ∑ w ∈ TT, (if G.Adj v w then 1 else 0) := by
        apply Finset.sum_congr rfl; intro v hv
        rw [h1 v, Finset.card_filter]
    _ = ∑ w ∈ TT, ∑ v ∈ S, (if G.Adj v w then 1 else 0) := Finset.sum_comm
    _ = ∑ w ∈ TT, (G.neighborFinset w ∩ S).card := by
        apply Finset.sum_congr rfl; intro w hw
        rw [h2 w, Finset.card_filter]
        apply Finset.sum_congr rfl; intro v hv
        simp only [SimpleGraph.adj_comm]

private lemma op309_ten_vertex_uniform_p3_host_selection_impossible_card_inter_three {α : Type*} [Fintype α] [DecidableEq α] (s A B C : Finset α)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hcover : A ∪ B ∪ C = Finset.univ) :
    (s ∩ A).card + (s ∩ B).card + (s ∩ C).card = s.card := by
  classical
  have hunion : (s ∩ A) ∪ (s ∩ B) ∪ (s ∩ C) = s := by
    ext w
    simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro ((⟨hw, _⟩ | ⟨hw, _⟩) | ⟨hw, _⟩) <;> exact hw
    · intro hw
      have hmem : w ∈ A ∪ B ∪ C := by rw [hcover]; exact Finset.mem_univ w
      rcases (Finset.mem_union.mp hmem) with hAB' | hC
      · rcases (Finset.mem_union.mp hAB') with hA | hB
        · exact Or.inl (Or.inl ⟨hw, hA⟩)
        · exact Or.inl (Or.inr ⟨hw, hB⟩)
      · exact Or.inr ⟨hw, hC⟩
  have hdAB : Disjoint (s ∩ A) (s ∩ B) := hAB.mono Finset.inter_subset_right Finset.inter_subset_right
  have hdAC : Disjoint (s ∩ A) (s ∩ C) := hAC.mono Finset.inter_subset_right Finset.inter_subset_right
  have hdBC : Disjoint (s ∩ B) (s ∩ C) := hBC.mono Finset.inter_subset_right Finset.inter_subset_right
  have hdAB_C : Disjoint ((s ∩ A) ∪ (s ∩ B)) (s ∩ C) := by
    rw [Finset.disjoint_union_left]; exact ⟨hdAC, hdBC⟩
  have hcard : ((s ∩ A) ∪ (s ∩ B) ∪ (s ∩ C)).card
      = (s ∩ A).card + (s ∩ B).card + (s ∩ C).card := by
    rw [Finset.card_union_of_disjoint hdAB_C, Finset.card_union_of_disjoint hdAB]
  rw [hunion] at hcard
  exact hcard.symm

private lemma op309_ten_vertex_uniform_p3_host_selection_impossible_card_inter_two {α : Type*} [DecidableEq α] (s A B : Finset α)
    (hAB : Disjoint A B) (hs : s ⊆ A ∪ B) :
    (s ∩ A).card + (s ∩ B).card = s.card := by
  classical
  have hunion : (s ∩ A) ∪ (s ∩ B) = s := by
    ext w; simp only [Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro (⟨hw,_⟩ | ⟨hw,_⟩) <;> exact hw
    · intro hw
      rcases Finset.mem_union.mp (hs hw) with h | h
      · exact Or.inl ⟨hw, h⟩
      · exact Or.inr ⟨hw, h⟩
  have hd : Disjoint (s ∩ A) (s ∩ B) := hAB.mono Finset.inter_subset_right Finset.inter_subset_right
  have hcard : ((s ∩ A) ∪ (s ∩ B)).card = (s ∩ A).card + (s ∩ B).card :=
    Finset.card_union_of_disjoint hd
  rw [hunion] at hcard
  exact hcard.symm

theorem op309_ten_vertex_uniform_p3_host_selection_impossible
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset G.edgeSet) :
    Fintype.card V = 10 →
    (∀ v, (G.neighborSet v).ncard = 3) →
    let d : V → ℕ := fun v => (R.filter fun e => v ∈ e.1).card
    (∀ v, d v ≤ 2) →
    (∀ u v, G.Adj u v → d u ≠ d v) →
    (∀ u v w, d u = 0 → G.Adj u v → G.Adj u w → d v = d w) →
    False := by
  classical
  intro hcard hdeg
  let d : V → ℕ := fun v => (R.filter fun e => v ∈ e.1).card
  change (∀ v, d v ≤ 2) → (∀ u v, G.Adj u v → d u ≠ d v) →
    (∀ u v w, d u = 0 → G.Adj u v → G.Adj u w → d v = d w) → False
  intro hle hadj hunif
  have hd : ∀ v, d v = (R.filter fun e => v ∈ e.1).card := fun v => rfl
  let Z : Finset V := Finset.univ.filter (fun v => d v = 0)
  let O : Finset V := Finset.univ.filter (fun v => d v = 1)
  let T : Finset V := Finset.univ.filter (fun v => d v = 2)
  let Za : Finset V := Z.filter (fun v => ∀ w, G.Adj v w → d w = 1)
  let Zb : Finset V := Z.filter (fun v => ∀ w, G.Adj v w → d w = 2)
  have memZ : ∀ v, v ∈ Z ↔ d v = 0 := by intro v; simp [Z]
  have memO : ∀ v, v ∈ O ↔ d v = 1 := by intro v; simp [O]
  have memT : ∀ v, v ∈ T ↔ d v = 2 := by intro v; simp [T]
  have memZa : ∀ v, v ∈ Za ↔ d v = 0 ∧ (∀ w, G.Adj v w → d w = 1) := by
    intro v; simp [Za, Z]
  have memZb : ∀ v, v ∈ Zb ↔ d v = 0 ∧ (∀ w, G.Adj v w → d w = 2) := by
    intro v; simp [Zb, Z]
  have hd012 : ∀ v, d v = 0 ∨ d v = 1 ∨ d v = 2 := by
    intro v; have := hle v; omega
  have hcover3 : Z ∪ O ∪ T = Finset.univ := by
    ext v
    simp only [Finset.mem_union, Finset.mem_univ]
    constructor
    · rintro _; exact trivial
    · intro _
      rcases hd012 v with h | h | h
      · exact Or.inl (Or.inl ((memZ v).mpr h))
      · exact Or.inl (Or.inr ((memO v).mpr h))
      · exact Or.inr ((memT v).mpr h)
  have hZO : Disjoint Z O := by
    rw [Finset.disjoint_left]; intro v hv hv'
    rw [memZ] at hv; rw [memO] at hv'; omega
  have hZT : Disjoint Z T := by
    rw [Finset.disjoint_left]; intro v hv hv'
    rw [memZ] at hv; rw [memT] at hv'; omega
  have hOT : Disjoint O T := by
    rw [Finset.disjoint_left]; intro v hv hv'
    rw [memO] at hv; rw [memT] at hv'; omega
  have hcardZOT : Z.card + O.card + T.card = 10 := by
    have h := op309_ten_vertex_uniform_p3_host_selection_impossible_card_inter_three (Finset.univ : Finset V) Z O T hZO hZT hOT hcover3
    simp only [Finset.univ_inter, Finset.card_univ, hcard] at h
    exact h
  have hdeg3 : ∀ v, G.degree v = 3 := by
    intro v
    rw [show G.degree v = (G.neighborSet v).ncard from by
      rw [← SimpleGraph.card_neighborSet_eq_degree, Set.ncard_eq_toFinset_card', ← Set.toFinset_card],
      hdeg v]
  have hnbrcard : ∀ v, (G.neighborFinset v).card = 3 := by
    intro v; rw [SimpleGraph.card_neighborFinset_eq_degree, hdeg3 v]
  have hnbr_ne : ∀ v, (G.neighborFinset v).Nonempty := by
    intro v
    have h : 0 < (G.neighborFinset v).card := by rw [hnbrcard v]; norm_num
    exact Finset.card_pos.mp h
  have hZa_sub : Za ⊆ Z := fun v hv => by rw [memZa] at hv; exact (memZ v).mpr hv.1
  have hZb_sub : Zb ⊆ Z := fun v hv => by rw [memZb] at hv; exact (memZ v).mpr hv.1
  have hZaZb_disj : Disjoint Za Zb := by
    rw [Finset.disjoint_left]
    intro v hv hv'
    rw [memZa] at hv; rw [memZb] at hv'
    obtain ⟨w, hw⟩ := hnbr_ne v
    rw [mem_neighborFinset] at hw
    have h1 := hv.2 w hw
    have h2 := hv'.2 w hw
    omega
  have hZaZb : Za ∪ Zb = Z := by
    ext v
    simp only [Finset.mem_union]
    constructor
    · rintro (h | h)
      · exact hZa_sub h
      · exact hZb_sub h
    · intro hv
      rw [memZ] at hv
      obtain ⟨w, hw⟩ := hnbr_ne v
      rw [mem_neighborFinset] at hw
      have hdw_ne : d w ≠ 0 := by
        intro h0; exact (hadj v w hw) (by rw [hv, h0])
      have hdw := hle w
      rcases (show d w = 1 ∨ d w = 2 by omega) with h1 | h2
      · left; rw [memZa]; exact ⟨hv, fun x hx => (hunif v w x hv hw hx).symm.trans h1⟩
      · right; rw [memZb]; exact ⟨hv, fun x hx => (hunif v w x hv hw hx).symm.trans h2⟩
  have hab : Za.card + Zb.card = Z.card := by
    have h := op309_ten_vertex_uniform_p3_host_selection_impossible_card_inter_two Z Za Zb hZaZb_disj (fun v hv => by rw [hZaZb]; exact hv)
    rwa [(Finset.inter_eq_right).mpr hZa_sub, (Finset.inter_eq_right).mpr hZb_sub] at h
  have hpart_nbr : ∀ v, (G.neighborFinset v ∩ Z).card + (G.neighborFinset v ∩ O).card
      + (G.neighborFinset v ∩ T).card = (G.neighborFinset v).card := by
    intro v
    exact op309_ten_vertex_uniform_p3_host_selection_impossible_card_inter_three (G.neighborFinset v) Z O T hZO hZT hOT hcover3
  have hnbrO0 : ∀ v, v ∈ O → (G.neighborFinset v ∩ O).card = 0 := by
    intro v hv
    rw [memO] at hv
    apply Finset.card_eq_zero.mpr
    rw [Finset.eq_empty_iff_forall_notMem]
    intro w hw
    rw [Finset.mem_inter, mem_neighborFinset, memO] at hw
    exact (hadj v w hw.1) (by rw [hv, hw.2])
  have hnbrOT : ∀ v, v ∈ O → (G.neighborFinset v ∩ Z).card + (G.neighborFinset v ∩ T).card = 3 := by
    intro v hv
    have hp := hpart_nbr v
    rw [hnbrO0 v hv, hnbrcard v] at hp
    omega
  have hR3 : 3 * O.card = (∑ v ∈ O, (G.neighborFinset v ∩ Z).card)
      + (∑ v ∈ O, (G.neighborFinset v ∩ T).card) := by
    have hsum : ∑ v ∈ O, ((G.neighborFinset v ∩ Z).card + (G.neighborFinset v ∩ T).card)
        = ∑ v ∈ O, (3:ℕ) := by
      apply Finset.sum_congr rfl; intro v hv; exact hnbrOT v hv
    rw [Finset.sum_add_distrib, Finset.sum_const_nat (fun _ _ => rfl)] at hsum
    rw [Nat.mul_comm] at hsum
    exact hsum.symm
  have hnbrT0 : ∀ v, v ∈ T → (G.neighborFinset v ∩ T).card = 0 := by
    intro v hv
    rw [memT] at hv
    apply Finset.card_eq_zero.mpr
    rw [Finset.eq_empty_iff_forall_notMem]
    intro w hw
    rw [Finset.mem_inter, mem_neighborFinset, memT] at hw
    exact (hadj v w hw.1) (by rw [hv, hw.2])
  have hnbrTZ : ∀ v, v ∈ T → (G.neighborFinset v ∩ Z).card + (G.neighborFinset v ∩ O).card = 3 := by
    intro v hv
    have hp := hpart_nbr v
    rw [hnbrT0 v hv, hnbrcard v] at hp
    omega
  have hR4 : 3 * T.card = (∑ v ∈ T, (G.neighborFinset v ∩ Z).card)
      + (∑ v ∈ T, (G.neighborFinset v ∩ O).card) := by
    have hsum : ∑ v ∈ T, ((G.neighborFinset v ∩ Z).card + (G.neighborFinset v ∩ O).card)
        = ∑ v ∈ T, (3:ℕ) := by
      apply Finset.sum_congr rfl; intro v hv; exact hnbrTZ v hv
    rw [Finset.sum_add_distrib, Finset.sum_const_nat (fun _ _ => rfl)] at hsum
    rw [Nat.mul_comm] at hsum
    exact hsum.symm
  have hnbrZa : ∀ w, w ∈ Za → (G.neighborFinset w ∩ O).card = 3 := by
    intro w hw
    rw [memZa] at hw
    have hsub : G.neighborFinset w ⊆ O := by
      intro x hx
      rw [mem_neighborFinset] at hx
      rw [memO]; exact hw.2 x hx
    rw [(Finset.inter_eq_left).mpr hsub, hnbrcard w]
  have hnbrZb_O : ∀ w, w ∈ Zb → (G.neighborFinset w ∩ O).card = 0 := by
    intro w hw
    rw [memZb] at hw
    apply Finset.card_eq_zero.mpr
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x hx
    rw [Finset.mem_inter, mem_neighborFinset, memO] at hx
    have h2 : d x = 2 := hw.2 x hx.1
    omega
  have hR5 : (∑ v ∈ O, (G.neighborFinset v ∩ Z).card) = 3 * Za.card := by
    rw [op309_ten_vertex_uniform_p3_host_selection_impossible_sum_nbr_comm G O Z, ← hZaZb, Finset.sum_union hZaZb_disj]
    rw [Finset.sum_const_nat (fun w hw => hnbrZa w hw),
        Finset.sum_eq_zero (fun w hw => hnbrZb_O w hw), Nat.add_zero, Nat.mul_comm]
  have hnbrZb : ∀ w, w ∈ Zb → (G.neighborFinset w ∩ T).card = 3 := by
    intro w hw
    rw [memZb] at hw
    have hsub : G.neighborFinset w ⊆ T := by
      intro x hx
      rw [mem_neighborFinset] at hx
      rw [memT]; exact hw.2 x hx
    rw [(Finset.inter_eq_left).mpr hsub, hnbrcard w]
  have hnbrZa_T : ∀ w, w ∈ Za → (G.neighborFinset w ∩ T).card = 0 := by
    intro w hw
    rw [memZa] at hw
    apply Finset.card_eq_zero.mpr
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x hx
    rw [Finset.mem_inter, mem_neighborFinset, memT] at hx
    have h1 : d x = 1 := hw.2 x hx.1
    omega
  have hR6 : (∑ v ∈ T, (G.neighborFinset v ∩ Z).card) = 3 * Zb.card := by
    rw [op309_ten_vertex_uniform_p3_host_selection_impossible_sum_nbr_comm G T Z, ← hZaZb, Finset.sum_union hZaZb_disj]
    rw [Finset.sum_eq_zero (fun w hw => hnbrZa_T w hw),
        Finset.sum_const_nat (fun w hw => hnbrZb w hw), Nat.zero_add, Nat.mul_comm]
  have hR7 : (∑ v ∈ T, (G.neighborFinset v ∩ O).card)
      = (∑ v ∈ O, (G.neighborFinset v ∩ T).card) := by
    rw [op309_ten_vertex_uniform_p3_host_selection_impossible_sum_nbr_comm G T O]
  have hOsel : (∑ v ∈ O, (R.filter fun e => v ∈ e.1).card) = O.card := by
    have h1 : ∀ v ∈ O, (R.filter fun e => v ∈ e.1).card = 1 := by
      intro v hv; rw [← hd v, (memO v).mp hv]
    calc (∑ v ∈ O, (R.filter fun e => v ∈ e.1).card) = ∑ v ∈ O, (1:ℕ) := Finset.sum_congr rfl h1
      _ = O.card := by simp
  have hTsel : (∑ v ∈ T, (R.filter fun e => v ∈ e.1).card) = T.card * 2 := by
    have h1 : ∀ v ∈ T, (R.filter fun e => v ∈ e.1).card = 2 := by
      intro v hv; rw [← hd v, (memT v).mp hv]
    calc (∑ v ∈ T, (R.filter fun e => v ∈ e.1).card) = ∑ v ∈ T, (2:ℕ) := Finset.sum_congr rfl h1
      _ = T.card * 2 := Finset.sum_const_nat (fun _ _ => rfl)
  have hOsel_rhs : (∑ e ∈ R, (O.filter fun w => w ∈ e.1).card) = R.card := by
    have h1 : ∀ e ∈ R, (O.filter fun w => w ∈ e.1).card = 1 := by
      intro e he; exact (op309_ten_vertex_uniform_p3_host_selection_impossible_sel_filters G R d hd hle hadj e he).1
    calc (∑ e ∈ R, (O.filter fun w => w ∈ e.1).card) = ∑ e ∈ R, (1:ℕ) := Finset.sum_congr rfl h1
      _ = R.card := by simp
  have hTsel_rhs : (∑ e ∈ R, (T.filter fun w => w ∈ e.1).card) = R.card := by
    have h1 : ∀ e ∈ R, (T.filter fun w => w ∈ e.1).card = 1 := by
      intro e he; exact (op309_ten_vertex_uniform_p3_host_selection_impossible_sel_filters G R d hd hle hadj e he).2
    calc (∑ e ∈ R, (T.filter fun w => w ∈ e.1).card) = ∑ e ∈ R, (1:ℕ) := Finset.sum_congr rfl h1
      _ = R.card := by simp
  have hoR : O.card = R.card := by
    rw [← hOsel, op309_ten_vertex_uniform_p3_host_selection_impossible_sel_double G R O, hOsel_rhs]
  have hcR : T.card * 2 = R.card := by
    rw [← hTsel, op309_ten_vertex_uniform_p3_host_selection_impossible_sel_double G R T, hTsel_rhs]
  have hnbrT_ge : ∀ v, v ∈ O → d v ≤ (G.neighborFinset v ∩ T).card := by
    intro v hv
    rw [memO] at hv
    have hpos : 0 < (R.filter fun e => v ∈ e.1).card := by rw [← hd v, hv]; norm_num
    obtain ⟨e0, he0⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_filter] at he0
    obtain ⟨he0R, hv_mem⟩ := he0
    obtain ⟨u, w, huw, heq, hdu, hdw⟩ := op309_ten_vertex_uniform_p3_host_selection_impossible_sel_oriented G R d hd hle hadj e0 he0R
    have hwT : w ∈ T := (memT w).mpr hdw
    rw [heq, Sym2.mem_iff] at hv_mem
    have hmem : w ∈ G.neighborFinset v ∩ T := by
      rw [Finset.mem_inter, mem_neighborFinset]
      refine ⟨?_, hwT⟩
      rcases hv_mem with hvu | hvw
      · rw [hvu]; exact huw
      · exfalso; rw [hvw] at hv; omega
    rw [hv]
    have hpos2 : 0 < (G.neighborFinset v ∩ T).card := Finset.card_pos.mpr ⟨w, hmem⟩
    omega
  have hR9 : R.card ≤ ∑ v ∈ O, (G.neighborFinset v ∩ T).card := by
    have hL : (∑ v ∈ O, d v) = R.card := by
      rw [show (∑ v ∈ O, d v) = (∑ v ∈ O, (R.filter fun e => v ∈ e.1).card) from
        Finset.sum_congr rfl (fun v hv => hd v), op309_ten_vertex_uniform_p3_host_selection_impossible_sel_double G R O, hOsel_rhs]
    rw [← hL]
    exact Finset.sum_le_sum (fun v hv => hnbrT_ge v hv)
  omega
