import AFTD.Prelude
import AFTD.Kb.Tcs.Op309BipartiteEighteenGraph
import AFTD.Kb.Tcs.Op309UniformRoleStructureBipartite

/-!
# op309_bipartite_eighteen_uniform_p3_host_selection_impossible

Topic: graphs   Node: 0fa26b2c67b0

Provenance: helper lemma. OP-309 experiments 42486–42490; graph definition already in knowledge base.

The previously recorded connected cubic girth-six bipartite 18-vertex graph has no uniform-host selected P3 forest.
-/

private instance op309_bipartite_eighteen_uniform_p3_host_selection_impossible_dec_rel :
    DecidableRel op309_bipartite_eighteen_graph.Adj :=
  fun u v => by unfold op309_bipartite_eighteen_graph; infer_instance

private lemma op309_bipartite_eighteen_uniform_p3_host_selection_impossible_dom :
    ∀ b t4 : Fin 18, t4 ≠ b → ¬ op309_bipartite_eighteen_graph.Adj b t4 →
      (Finset.biUnion (op309_bipartite_eighteen_graph.neighborFinset b ∪ {t4})
        (fun t => op309_bipartite_eighteen_graph.neighborFinset t)).card ≠ 9 := by
  decide

private lemma op309_bipartite_eighteen_uniform_p3_host_selection_impossible_card_inter_three {α : Type*} [Fintype α] [DecidableEq α]
    (s A B C : Finset α) (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hcover : A ∪ B ∪ C = Finset.univ) :
    (s ∩ A).card + (s ∩ B).card + (s ∩ C).card = s.card := by
  have hsub : s ⊆ A ∪ B ∪ C := by rw [hcover]; exact Finset.subset_univ s
  have hunion : (s ∩ A) ∪ (s ∩ B) ∪ (s ∩ C) = s := by
    have h1 : (s ∩ A) ∪ (s ∩ B) ∪ (s ∩ C) = s ∩ (A ∪ B ∪ C) := by
      ext x; simp only [Finset.mem_union, Finset.mem_inter]; tauto
    rw [h1, Finset.inter_eq_left.mpr hsub]
  have hdAB : Disjoint (s ∩ A) (s ∩ B) := by
    rw [Finset.disjoint_left]; intro x hx hx'
    rw [Finset.mem_inter] at hx hx'
    exact (Finset.disjoint_left.mp hAB hx.2 hx'.2)
  have hdAC : Disjoint (s ∩ A) (s ∩ C) := by
    rw [Finset.disjoint_left]; intro x hx hx'
    rw [Finset.mem_inter] at hx hx'
    exact (Finset.disjoint_left.mp hAC hx.2 hx'.2)
  have hdBC : Disjoint (s ∩ B) (s ∩ C) := by
    rw [Finset.disjoint_left]; intro x hx hx'
    rw [Finset.mem_inter] at hx hx'
    exact (Finset.disjoint_left.mp hBC hx.2 hx'.2)
  have hd2 : Disjoint ((s ∩ A) ∪ (s ∩ B)) (s ∩ C) := by
    rw [Finset.disjoint_left]; intro x hx hx'
    rw [Finset.mem_union] at hx
    rcases hx with hx | hx
    · exact (Finset.disjoint_left.mp hdAC hx hx')
    · exact (Finset.disjoint_left.mp hdBC hx hx')
  rw [← Finset.card_union_of_disjoint hdAB, ← Finset.card_union_of_disjoint hd2, hunion]

private lemma op309_bipartite_eighteen_uniform_p3_host_selection_impossible_sum_nbr_comm {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S TT : Finset V) :
    ∑ v ∈ S, (G.neighborFinset v ∩ TT).card = ∑ w ∈ TT, (G.neighborFinset w ∩ S).card := by
  have h1 : ∀ v : V, (G.neighborFinset v ∩ TT).card = ∑ w ∈ TT, if G.Adj v w then 1 else 0 := by
    intro v
    have hvv : (G.neighborFinset v ∩ TT) = TT.filter (fun w => G.Adj v w) := by
      ext w; rw [Finset.mem_inter, Finset.mem_filter, SimpleGraph.mem_neighborFinset]; tauto
    rw [hvv, Finset.card_eq_sum_ones, Finset.sum_filter]
  simp_rw [h1]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  have h2 : (G.neighborFinset w ∩ S).card = ∑ v ∈ S, if G.Adj w v then 1 else 0 := by
    have hvv : (G.neighborFinset w ∩ S) = S.filter (fun v => G.Adj w v) := by
      ext v; rw [Finset.mem_inter, Finset.mem_filter, SimpleGraph.mem_neighborFinset]; tauto
    rw [hvv, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [h2]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases h : G.Adj v w
  · rw [if_pos h, if_pos ((SimpleGraph.adj_comm G v w).mp h)]
  · rw [if_neg h, if_neg (fun hh => h ((SimpleGraph.adj_comm G v w).mpr hh))]

private lemma op309_bipartite_eighteen_uniform_p3_host_selection_impossible_sel_double {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (R : Finset G.edgeSet) (S : Finset V) :
    ∑ v ∈ S, (R.filter fun e => v ∈ e.1).card = ∑ e ∈ R, (S.filter fun w => w ∈ e.1).card := by
  have h1 : ∀ v : V, (R.filter fun e => v ∈ e.1).card = ∑ e ∈ R, if v ∈ e.1 then 1 else 0 := by
    intro v
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp_rw [h1]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  have h2 : (S.filter fun w => w ∈ e.1).card = ∑ w ∈ S, if w ∈ e.1 then 1 else 0 := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [h2]

private lemma op309_bipartite_eighteen_uniform_p3_host_selection_impossible_sel_oriented {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (R : Finset G.edgeSet) (d : V → ℕ)
    (hd : ∀ v, d v = (R.filter fun e => v ∈ e.1).card)
    (hle : ∀ v, d v ≤ 2) (hadj : ∀ u v, G.Adj u v → d u ≠ d v)
    (e : G.edgeSet) (he : e ∈ R) :
    ∃ u v, G.Adj u v ∧ ↑e = s(u,v) ∧ d u = 1 ∧ d v = 2 := by
  obtain ⟨u, v, huv⟩ := Sym2.exists.mp (show ∃ x : Sym2 V, x = (e.1 : Sym2 V) from ⟨e.1, rfl⟩)
  have heq : (e.1 : Sym2 V) = s(u,v) := huv.symm
  have hmems : s(u,v) ∈ G.edgeSet := huv ▸ e.2
  have hadjuv : G.Adj u v := (SimpleGraph.mem_edgeSet G).mp hmems
  have hu : u ∈ (e.1 : Sym2 V) := by rw [heq]; exact Sym2.mem_mk_left u v
  have hv : v ∈ (e.1 : Sym2 V) := by rw [heq]; exact Sym2.mem_mk_right u v
  have hupos : 0 < (R.filter fun e' => u ∈ e'.1).card :=
    Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hu⟩⟩
  have hvpos : 0 < (R.filter fun e' => v ∈ e'.1).card :=
    Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hv⟩⟩
  have hdupos : 0 < d u := by rw [hd u]; exact hupos
  have hdvpos : 0 < d v := by rw [hd v]; exact hvpos
  have hdu : d u = 1 ∨ d u = 2 := by have := hle u; omega
  have hdv : d v = 1 ∨ d v = 2 := by have := hle v; omega
  rcases hdu with hdu1 | hdu2
  · rcases hdv with hdv1 | hdv2
    · exact absurd (by rw [hdu1, hdv1]) (hadj u v hadjuv)
    · exact ⟨u, v, hadjuv, heq, hdu1, hdv2⟩
  · rcases hdv with hdv1 | hdv2
    · exact ⟨v, u, hadjuv.symm, heq.trans Sym2.eq_swap, hdv1, hdu2⟩
    · exact absurd (by rw [hdu2, hdv2]) (hadj u v hadjuv)

private lemma op309_bipartite_eighteen_uniform_p3_host_selection_impossible_sel_filters {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (R : Finset G.edgeSet) (d : V → ℕ)
    (hd : ∀ v, d v = (R.filter fun e => v ∈ e.1).card)
    (hle : ∀ v, d v ≤ 2) (hadj : ∀ u v, G.Adj u v → d u ≠ d v)
    (e : G.edgeSet) (he : e ∈ R) :
    ((Finset.univ.filter (fun w => d w = 1)).filter (fun w => w ∈ e.1)).card = 1 ∧
    ((Finset.univ.filter (fun w => d w = 2)).filter (fun w => w ∈ e.1)).card = 1 := by
  obtain ⟨u, v, huv, heq, hdu, hdv⟩ := op309_bipartite_eighteen_uniform_p3_host_selection_impossible_sel_oriented G R d hd hle hadj e he
  constructor
  · have hset : (Finset.univ.filter (fun w => d w = 1)).filter (fun w => w ∈ (e.1 : Sym2 V)) = {u} := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rw [heq, Sym2.mem_iff]
      constructor
      · rintro ⟨h1, h2 | h2⟩
        · exact h2
        · rw [h2] at h1; omega
      · intro h; rw [h]; exact ⟨hdu, Or.inl rfl⟩
    rw [hset]; simp
  · have hset : (Finset.univ.filter (fun w => d w = 2)).filter (fun w => w ∈ (e.1 : Sym2 V)) = {v} := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rw [heq, Sym2.mem_iff]
      constructor
      · rintro ⟨h1, h2 | h2⟩
        · rw [h2] at h1; omega
        · exact h2
      · intro h; rw [h]; exact ⟨hdv, Or.inr rfl⟩
    rw [hset]; simp

theorem op309_bipartite_eighteen_uniform_p3_host_selection_impossible
    (R : Finset op309_bipartite_eighteen_graph.edgeSet) :
    let G := op309_bipartite_eighteen_graph
    let d : Fin 18 → ℕ := fun v => (R.filter fun e => v ∈ e.1).card
    (∀ v, d v ≤ 2) →
    (∀ u v, G.Adj u v → d u ≠ d v) →
    (∀ u v w, d u = 0 → G.Adj u v → G.Adj u w → d v = d w) →
    False := by
  classical
  let G : SimpleGraph (Fin 18) := op309_bipartite_eighteen_graph
  let d : Fin 18 → ℕ := fun v => (R.filter fun e => v ∈ e.1).card
  change (∀ v, d v ≤ 2) → (∀ u v, G.Adj u v → d u ≠ d v) →
    (∀ u v w, d u = 0 → G.Adj u v → G.Adj u w → d v = d w) → False
  intro hle hadj hunif
  have hd : ∀ v, d v = (R.filter fun e => v ∈ e.1).card := fun v => rfl
  let Z : Finset (Fin 18) := Finset.univ.filter (fun v => d v = 0)
  let O : Finset (Fin 18) := Finset.univ.filter (fun v => d v = 1)
  let T : Finset (Fin 18) := Finset.univ.filter (fun v => d v = 2)
  let Za : Finset (Fin 18) := Z.filter (fun v => ∀ w, G.Adj v w → d w = 1)
  let Zb : Finset (Fin 18) := Z.filter (fun v => ∀ w, G.Adj v w → d w = 2)
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
  have hpart : Z.card + O.card + T.card = 18 := by
    have h := op309_bipartite_eighteen_uniform_p3_host_selection_impossible_card_inter_three
      (Finset.univ : Finset (Fin 18)) Z O T hZO hZT hOT hcover3
    simp only [Finset.univ_inter, Finset.card_univ, Fintype.card_fin] at h
    exact h
  have hnbrcard : ∀ v, (G.neighborFinset v).card = 3 := by decide
  have hmemN : ∀ u v, v ∈ G.neighborFinset u ↔ G.Adj u v := fun u v => by
    rw [SimpleGraph.mem_neighborFinset]
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
    rw [SimpleGraph.mem_neighborFinset] at hw
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
      rw [SimpleGraph.mem_neighborFinset] at hw
      have hdw_ne : d w ≠ 0 := by
        intro h0; exact (hadj v w hw) (by rw [hv, h0])
      have hdw := hle w
      rcases (show d w = 1 ∨ d w = 2 by omega) with h1 | h2
      · left; rw [memZa]; exact ⟨hv, fun x hx => (hunif v w x hv hw hx).symm.trans h1⟩
      · right; rw [memZb]; exact ⟨hv, fun x hx => (hunif v w x hv hw hx).symm.trans h2⟩
  have hab : Za.card + Zb.card = Z.card := by
    rw [← Finset.card_union_of_disjoint hZaZb_disj, hZaZb]
  have hpart_nbr : ∀ v, (G.neighborFinset v ∩ Z).card + (G.neighborFinset v ∩ O).card
      + (G.neighborFinset v ∩ T).card = (G.neighborFinset v).card := by
    intro v
    exact op309_bipartite_eighteen_uniform_p3_host_selection_impossible_card_inter_three
      (G.neighborFinset v) Z O T hZO hZT hOT hcover3
  have hnbrO0 : ∀ v, v ∈ O → (G.neighborFinset v ∩ O).card = 0 := by
    intro v hv
    rw [memO] at hv
    apply Finset.card_eq_zero.mpr
    rw [Finset.eq_empty_iff_forall_notMem]
    intro w hw
    rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset, memO] at hw
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
    rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset, memT] at hw
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
      rw [SimpleGraph.mem_neighborFinset] at hx
      rw [memO]; exact hw.2 x hx
    rw [(Finset.inter_eq_left).mpr hsub, hnbrcard w]
  have hnbrZb_O : ∀ w, w ∈ Zb → (G.neighborFinset w ∩ O).card = 0 := by
    intro w hw
    rw [memZb] at hw
    apply Finset.card_eq_zero.mpr
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x hx
    rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset, memO] at hx
    have h2 : d x = 2 := hw.2 x hx.1
    omega
  have hR5 : (∑ v ∈ O, (G.neighborFinset v ∩ Z).card) = 3 * Za.card := by
    rw [op309_bipartite_eighteen_uniform_p3_host_selection_impossible_sum_nbr_comm G O Z, ← hZaZb, Finset.sum_union hZaZb_disj]
    rw [Finset.sum_const_nat (fun w hw => hnbrZa w hw),
        Finset.sum_eq_zero (fun w hw => hnbrZb_O w hw), Nat.add_zero, Nat.mul_comm]
  have hnbrZb : ∀ w, w ∈ Zb → (G.neighborFinset w ∩ T).card = 3 := by
    intro w hw
    rw [memZb] at hw
    have hsub : G.neighborFinset w ⊆ T := by
      intro x hx
      rw [SimpleGraph.mem_neighborFinset] at hx
      rw [memT]; exact hw.2 x hx
    rw [(Finset.inter_eq_left).mpr hsub, hnbrcard w]
  have hnbrZa_T : ∀ w, w ∈ Za → (G.neighborFinset w ∩ T).card = 0 := by
    intro w hw
    rw [memZa] at hw
    apply Finset.card_eq_zero.mpr
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x hx
    rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset, memT] at hx
    have h1 : d x = 1 := hw.2 x hx.1
    omega
  have hR6 : (∑ v ∈ T, (G.neighborFinset v ∩ Z).card) = 3 * Zb.card := by
    rw [op309_bipartite_eighteen_uniform_p3_host_selection_impossible_sum_nbr_comm G T Z, ← hZaZb, Finset.sum_union hZaZb_disj]
    rw [Finset.sum_eq_zero (fun w hw => hnbrZa_T w hw),
        Finset.sum_const_nat (fun w hw => hnbrZb w hw), Nat.zero_add, Nat.mul_comm]
  have hR7 : (∑ v ∈ T, (G.neighborFinset v ∩ O).card)
      = (∑ v ∈ O, (G.neighborFinset v ∩ T).card) := by
    rw [op309_bipartite_eighteen_uniform_p3_host_selection_impossible_sum_nbr_comm G T O]
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
      intro e he; exact (op309_bipartite_eighteen_uniform_p3_host_selection_impossible_sel_filters G R d hd hle hadj e he).1
    calc (∑ e ∈ R, (O.filter fun w => w ∈ e.1).card) = ∑ e ∈ R, (1:ℕ) := Finset.sum_congr rfl h1
      _ = R.card := by simp
  have hTsel_rhs : (∑ e ∈ R, (T.filter fun w => w ∈ e.1).card) = R.card := by
    have h1 : ∀ e ∈ R, (T.filter fun w => w ∈ e.1).card = 1 := by
      intro e he; exact (op309_bipartite_eighteen_uniform_p3_host_selection_impossible_sel_filters G R d hd hle hadj e he).2
    calc (∑ e ∈ R, (T.filter fun w => w ∈ e.1).card) = ∑ e ∈ R, (1:ℕ) := Finset.sum_congr rfl h1
      _ = R.card := by simp
  have hoR : O.card = R.card := by
    rw [← hOsel, op309_bipartite_eighteen_uniform_p3_host_selection_impossible_sel_double G R O, hOsel_rhs]
  have hcR : T.card * 2 = R.card := by
    rw [← hTsel, op309_bipartite_eighteen_uniform_p3_host_selection_impossible_sel_double G R T, hTsel_rhs]
  have hnbrT_ge : ∀ v, v ∈ O → d v ≤ (G.neighborFinset v ∩ T).card := by
    intro v hv
    rw [memO] at hv
    have hpos : 0 < (R.filter fun e => v ∈ e.1).card := by rw [← hd v, hv]; norm_num
    obtain ⟨e0, he0⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_filter] at he0
    obtain ⟨he0R, hv_mem⟩ := he0
    obtain ⟨u, w, huw, heq, hdu, hdw⟩ := op309_bipartite_eighteen_uniform_p3_host_selection_impossible_sel_oriented G R d hd hle hadj e0 he0R
    have hwT : w ∈ T := (memT w).mpr hdw
    rw [heq, Sym2.mem_iff] at hv_mem
    have hmem : w ∈ G.neighborFinset v ∩ T := by
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
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
        Finset.sum_congr rfl (fun v hv => hd v),
        op309_bipartite_eighteen_uniform_p3_host_selection_impossible_sel_double G R O, hOsel_rhs]
    rw [← hL]
    exact Finset.sum_le_sum (fun v hv => hnbrT_ge v hv)
  have hT4 : T.card = 4 := by omega
  have hO8 : O.card = 8 := by omega
  have hZb1 : Zb.card = 1 := by omega
  obtain ⟨b, hZb_eq⟩ := Finset.card_eq_one.mp hZb1
  have hbmem : b ∈ Zb := by rw [hZb_eq]; simp
  have hb0 : d b = 0 := ((memZb b).mp hbmem).1
  have hbuni : ∀ w, G.Adj b w → d w = 2 := ((memZb b).mp hbmem).2
  have hNsubT : G.neighborFinset b ⊆ T := by
    intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw
    exact (memT w).mpr (hbuni w hw)
  have hNcard : (G.neighborFinset b).card = 3 := hnbrcard b
  have hex : ∃ t4, t4 ∈ T ∧ t4 ∉ G.neighborFinset b := by
    by_contra h
    push_neg at h
    have hsub : T ⊆ G.neighborFinset b := fun x hx => h x hx
    have := Finset.card_le_card hsub
    omega
  obtain ⟨t4, ht4T, ht4notN⟩ := hex
  have hne : t4 ≠ b := by
    intro h; rw [h] at ht4T
    have : d b = 2 := (memT b).mp ht4T
    omega
  have hnotadj : ¬ G.Adj b t4 := by
    intro h; exact ht4notN ((hmemN b t4).mpr h)
  have hT_eq : T = G.neighborFinset b ∪ {t4} := by
    have hdiffcard : (T \ G.neighborFinset b).card = 1 := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hNsubT, hT4, hNcard]
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hdiffcard
    apply Finset.Subset.antisymm
    · intro v hv
      rw [Finset.mem_union]
      by_cases h : v ∈ G.neighborFinset b
      · exact Or.inl h
      · right
        have hvx : v = x := by
          have hmem : v ∈ ({x} : Finset (Fin 18)) := by
            rw [← hx]; exact Finset.mem_sdiff.mpr ⟨hv, h⟩
          simpa using hmem
        have ht4x : t4 = x := by
          have hmem : t4 ∈ ({x} : Finset (Fin 18)) := by
            rw [← hx]; exact Finset.mem_sdiff.mpr ⟨ht4T, ht4notN⟩
          simpa using hmem
        rw [Finset.mem_singleton, hvx, ht4x]
    · intro v hv
      rcases Finset.mem_union.mp hv with h | h
      · exact hNsubT h
      · rw [Finset.mem_singleton] at h; rw [h]; exact ht4T
  let NT : Finset (Fin 18) := T.biUnion (fun t => G.neighborFinset t)
  have hmemNT : ∀ v, v ∈ NT ↔ ∃ t ∈ T, G.Adj t v := by
    intro v
    change v ∈ T.biUnion (fun t => G.neighborFinset t) ↔ _
    rw [Finset.mem_biUnion]
    simp [SimpleGraph.mem_neighborFinset]
  have hNT_to : ∀ v, v ∈ NT → v ∈ O ∨ v = b := by
    intro v hvNT
    obtain ⟨t, htT, htv⟩ := (hmemNT v).mp hvNT
    have hdt : d t = 2 := (memT t).mp htT
    have hdv_ne2 : d v ≠ 2 := by intro h; exact (hadj t v htv) (by rw [hdt, h])
    rcases hd012 v with h0 | h1 | h2
    · right
      have hvZb : v ∈ Zb := (memZb v).mpr ⟨h0, fun w hw => by
        have hh := hunif v t w h0 htv.symm hw
        rw [hdt] at hh; exact hh.symm⟩
      rw [hZb_eq] at hvZb
      simpa using hvZb
    · exact Or.inl ((memO v).mpr h1)
    · exact absurd h2 hdv_ne2
  have hO_eq : O = NT.erase b := by
    ext v
    rw [Finset.mem_erase]
    constructor
    · intro hv
      have hvb : v ≠ b := by
        intro h; rw [h] at hv; have := (memO b).mp hv; omega
      refine ⟨hvb, ?_⟩
      have hv1 : d v = 1 := (memO v).mp hv
      rw [hmemNT]
      have hpos : 0 < (R.filter fun e => v ∈ e.1).card := by rw [← hd v, hv1]; norm_num
      obtain ⟨e0, he0⟩ := Finset.card_pos.mp hpos
      rw [Finset.mem_filter] at he0
      obtain ⟨he0R, hv_mem⟩ := he0
      obtain ⟨u, w, huw, heq, hdu, hdw⟩ := op309_bipartite_eighteen_uniform_p3_host_selection_impossible_sel_oriented G R d hd hle hadj e0 he0R
      have hwT : w ∈ T := (memT w).mpr hdw
      rw [heq, Sym2.mem_iff] at hv_mem
      rcases hv_mem with hvu | hvw
      · exact ⟨w, hwT, by rw [hvu]; exact huw.symm⟩
      · exfalso; rw [hvw] at hv1; omega
    · rintro ⟨hvb, hvNT⟩
      rcases hNT_to v hvNT with h | h
      · exact h
      · exact absurd h hvb
  have hbNT : b ∈ NT := by
    rw [hmemNT]
    obtain ⟨t, ht⟩ := hnbr_ne b
    rw [SimpleGraph.mem_neighborFinset] at ht
    exact ⟨t, hNsubT ((hmemN b t).mpr ht), ht.symm⟩
  have hNTcard : NT.card = 9 := by
    rw [hO_eq] at hO8
    rw [Finset.card_erase_of_mem hbNT] at hO8
    omega
  have hNT_eq : NT = Finset.biUnion (G.neighborFinset b ∪ {t4}) (fun t => G.neighborFinset t) := by
    change T.biUnion (fun t => G.neighborFinset t) = _
    rw [hT_eq]
  have hchk := op309_bipartite_eighteen_uniform_p3_host_selection_impossible_dom b t4 hne hnotadj
  rw [← hNT_eq] at hchk
  exact hchk hNTcard
