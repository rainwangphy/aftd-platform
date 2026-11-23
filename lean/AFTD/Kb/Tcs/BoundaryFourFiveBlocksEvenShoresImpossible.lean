import AFTD.Prelude
import AFTD.Kb.Tcs.BoundaryFiveBlocksVertexNonneighborDefects
import AFTD.Kb.Tcs.FinsetCardEqSumFourBlockInter

/-!
# boundary_four_five_blocks_even_shores_impossible

Topic: graphs   Node: a55e2d5073c3

Provenance: helper lemma. OP-1957: even-shore obstruction for the four-five-block boundary case.

In a 20-vertex graph partitioned into four five-vertex blocks A, B, C, D with A anticomplete to B and C anticomplete to D, minimum degree at least 12 precludes two disjoint even sets Q and W with eight vertices in total that avoid x in A and y in C, with Q anticomplete to y and W, and W anticomplete to x.
-/

private lemma boundary_four_five_blocks_even_shores_impossible_generic_bound
    (G : SimpleGraph (Fin 20)) [DecidableRel G.Adj]
    (hdegree : ∀ v, 12 ≤ (G.neighborFinset v).card)
    (v : Fin 20) (F S : Finset (Fin 20))
    (hFcard : F.card = 5) (hvF : v ∉ F) (hFadj : ∀ f ∈ F, ¬ G.Adj v f)
    (hS : ∀ s ∈ S, s ≠ v ∧ ¬ G.Adj v s) : (S \ F).card ≤ 2 := by
  have hdeg : 12 ≤ (G.neighborFinset v).card := hdegree v
  set NN := Finset.univ \ (G.neighborFinset v ∪ {v}) with hNN
  have hv : v ∉ G.neighborFinset v := by simp [SimpleGraph.mem_neighborFinset]
  have hdisj : Disjoint (G.neighborFinset v) {v} := Finset.disjoint_singleton_right.mpr hv
  have hcardX : (G.neighborFinset v ∪ {v}).card = (G.neighborFinset v).card + 1 := by
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_singleton]
  have hle19 : (G.neighborFinset v).card ≤ 19 := by
    have hsub : G.neighborFinset v ⊆ Finset.univ.erase v := by
      intro w hw
      simp only [Finset.mem_erase, SimpleGraph.mem_neighborFinset] at hw ⊢
      exact ⟨fun h => by subst h; exact G.irrefl hw, Finset.mem_univ w⟩
    calc (G.neighborFinset v).card ≤ (Finset.univ.erase v).card := Finset.card_le_card hsub
      _ = 20 - 1 := by rw [Finset.card_erase_of_mem (Finset.mem_univ v)]; simp
      _ = 19 := by norm_num
  have hNNcard : NN.card ≤ 7 := by
    have hcs : NN.card = (Finset.univ : Finset (Fin 20)).card
        - ((G.neighborFinset v ∪ {v}) ∩ (Finset.univ : Finset (Fin 20))).card := by
      rw [hNN]; exact Finset.card_sdiff
    rw [Finset.inter_univ] at hcs
    rw [hcs, hcardX]
    have h20 : (Finset.univ : Finset (Fin 20)).card = 20 := by simp
    rw [h20]; omega
  have hSsub : S ⊆ NN := by
    intro s hs
    obtain ⟨hsv, hsadj⟩ := hS s hs
    rw [hNN, Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton, SimpleGraph.mem_neighborFinset]
    exact ⟨Finset.mem_univ _, by simp [hsadj, hsv]⟩
  have hFsub : F ⊆ NN := by
    intro f hf
    have hfv : f ≠ v := fun h => hvF (h ▸ hf)
    have hfadj := hFadj f hf
    rw [hNN, Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton, SimpleGraph.mem_neighborFinset]
    exact ⟨Finset.mem_univ _, by simp [hfadj, hfv]⟩
  have hsub2 : S \ F ⊆ NN \ F := by
    intro xx hx
    rw [Finset.mem_sdiff] at hx ⊢
    exact ⟨hSsub hx.1, hx.2⟩
  have hinter : F ∩ NN = F := Finset.inter_eq_left.mpr hFsub
  calc (S \ F).card ≤ (NN \ F).card := Finset.card_le_card hsub2
    _ = NN.card - (F ∩ NN).card := Finset.card_sdiff
    _ = NN.card - 5 := by rw [hinter, hFcard]
    _ ≤ 7 - 5 := by omega
    _ = 2 := by norm_num

private lemma boundary_four_five_blocks_even_shores_impossible_contra
    (G : SimpleGraph (Fin 20)) [DecidableRel G.Adj]
    (hdegree : ∀ v, 12 ≤ (G.neighborFinset v).card)
    (v : Fin 20) (F S : Finset (Fin 20))
    (hFcard : F.card = 5) (hvF : v ∉ F) (hFadj : ∀ f ∈ F, ¬ G.Adj v f)
    (hScard : 3 ≤ S.card) (hS : ∀ s ∈ S, s ≠ v ∧ ¬ G.Adj v s)
    (hSF : ∀ s ∈ S, s ∉ F) : False := by
  have hb := boundary_four_five_blocks_even_shores_impossible_generic_bound G hdegree v F S hFcard hvF hFadj hS
  have hsub : S ⊆ S \ F := by
    intro xx hxx; rw [Finset.mem_sdiff]; exact ⟨hxx, hSF xx hxx⟩
  have := Finset.card_le_card hsub
  omega

private lemma boundary_four_five_blocks_even_shores_impossible_contraA
    (G : SimpleGraph (Fin 20)) [DecidableRel G.Adj]
    (hdegree : ∀ v, 12 ≤ (G.neighborFinset v).card)
    (A B : Finset (Fin 20)) (hAB : Disjoint A B) (hB : B.card = 5)
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (v : Fin 20) (hv : v ∈ A) (S : Finset (Fin 20))
    (hScard : 3 ≤ S.card) (hS : ∀ s ∈ S, s ≠ v ∧ ¬ G.Adj v s)
    (hSF : ∀ s ∈ S, s ∉ B) : False :=
  boundary_four_five_blocks_even_shores_impossible_contra G hdegree v B S hB (fun h => (Finset.disjoint_left.mp hAB) hv h)
    (fun b hb => hnoAB v hv b hb) hScard hS hSF

private lemma boundary_four_five_blocks_even_shores_impossible_contraB
    (G : SimpleGraph (Fin 20)) [DecidableRel G.Adj]
    (hdegree : ∀ v, 12 ≤ (G.neighborFinset v).card)
    (A B : Finset (Fin 20)) (hAB : Disjoint A B) (hA : A.card = 5)
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (v : Fin 20) (hv : v ∈ B) (S : Finset (Fin 20))
    (hScard : 3 ≤ S.card) (hS : ∀ s ∈ S, s ≠ v ∧ ¬ G.Adj v s)
    (hSF : ∀ s ∈ S, s ∉ A) : False :=
  boundary_four_five_blocks_even_shores_impossible_contra G hdegree v A S hA (fun h => (Finset.disjoint_left.mp hAB) h hv)
    (fun a ha hadj => hnoAB a ha v hv ((G.adj_comm v a).mp hadj)) hScard hS hSF

private lemma boundary_four_five_blocks_even_shores_impossible_contraC
    (G : SimpleGraph (Fin 20)) [DecidableRel G.Adj]
    (hdegree : ∀ v, 12 ≤ (G.neighborFinset v).card)
    (C D : Finset (Fin 20)) (hCD : Disjoint C D) (hD : D.card = 5)
    (hnoCD : ∀ c ∈ C, ∀ d ∈ D, ¬ G.Adj c d)
    (v : Fin 20) (hv : v ∈ C) (S : Finset (Fin 20))
    (hScard : 3 ≤ S.card) (hS : ∀ s ∈ S, s ≠ v ∧ ¬ G.Adj v s)
    (hSF : ∀ s ∈ S, s ∉ D) : False :=
  boundary_four_five_blocks_even_shores_impossible_contra G hdegree v D S hD (fun h => (Finset.disjoint_left.mp hCD) hv h)
    (fun d hd => hnoCD v hv d hd) hScard hS hSF

private lemma boundary_four_five_blocks_even_shores_impossible_contraD
    (G : SimpleGraph (Fin 20)) [DecidableRel G.Adj]
    (hdegree : ∀ v, 12 ≤ (G.neighborFinset v).card)
    (C D : Finset (Fin 20)) (hCD : Disjoint C D) (hC : C.card = 5)
    (hnoCD : ∀ c ∈ C, ∀ d ∈ D, ¬ G.Adj c d)
    (v : Fin 20) (hv : v ∈ D) (S : Finset (Fin 20))
    (hScard : 3 ≤ S.card) (hS : ∀ s ∈ S, s ≠ v ∧ ¬ G.Adj v s)
    (hSF : ∀ s ∈ S, s ∉ C) : False :=
  boundary_four_five_blocks_even_shores_impossible_contra G hdegree v C S hC (fun h => (Finset.disjoint_left.mp hCD) h hv)
    (fun c hc hadj => hnoCD c hc v hv ((G.adj_comm v c).mp hadj)) hScard hS hSF

private lemma boundary_four_five_blocks_even_shores_impossible_boundA
    (G : SimpleGraph (Fin 20)) [DecidableRel G.Adj]
    (hdegree : ∀ v, 12 ≤ (G.neighborFinset v).card)
    (A B : Finset (Fin 20)) (hAB : Disjoint A B) (hB : B.card = 5)
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (v : Fin 20) (hv : v ∈ A) (S : Finset (Fin 20))
    (hS : ∀ s ∈ S, s ≠ v ∧ ¬ G.Adj v s) : (S \ B).card ≤ 2 :=
  boundary_four_five_blocks_even_shores_impossible_generic_bound G hdegree v B S hB (fun h => (Finset.disjoint_left.mp hAB) hv h)
    (fun b hb => hnoAB v hv b hb) hS

private lemma boundary_four_five_blocks_even_shores_impossible_boundB
    (G : SimpleGraph (Fin 20)) [DecidableRel G.Adj]
    (hdegree : ∀ v, 12 ≤ (G.neighborFinset v).card)
    (A B : Finset (Fin 20)) (hAB : Disjoint A B) (hA : A.card = 5)
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (v : Fin 20) (hv : v ∈ B) (S : Finset (Fin 20))
    (hS : ∀ s ∈ S, s ≠ v ∧ ¬ G.Adj v s) : (S \ A).card ≤ 2 :=
  boundary_four_five_blocks_even_shores_impossible_generic_bound G hdegree v A S hA (fun h => (Finset.disjoint_left.mp hAB) h hv)
    (fun a ha hadj => hnoAB a ha v hv ((G.adj_comm v a).mp hadj)) hS

private lemma boundary_four_five_blocks_even_shores_impossible_boundC
    (G : SimpleGraph (Fin 20)) [DecidableRel G.Adj]
    (hdegree : ∀ v, 12 ≤ (G.neighborFinset v).card)
    (C D : Finset (Fin 20)) (hCD : Disjoint C D) (hD : D.card = 5)
    (hnoCD : ∀ c ∈ C, ∀ d ∈ D, ¬ G.Adj c d)
    (v : Fin 20) (hv : v ∈ C) (S : Finset (Fin 20))
    (hS : ∀ s ∈ S, s ≠ v ∧ ¬ G.Adj v s) : (S \ D).card ≤ 2 :=
  boundary_four_five_blocks_even_shores_impossible_generic_bound G hdegree v D S hD (fun h => (Finset.disjoint_left.mp hCD) hv h)
    (fun d hd => hnoCD v hv d hd) hS

private lemma boundary_four_five_blocks_even_shores_impossible_boundD
    (G : SimpleGraph (Fin 20)) [DecidableRel G.Adj]
    (hdegree : ∀ v, 12 ≤ (G.neighborFinset v).card)
    (C D : Finset (Fin 20)) (hCD : Disjoint C D) (hC : C.card = 5)
    (hnoCD : ∀ c ∈ C, ∀ d ∈ D, ¬ G.Adj c d)
    (v : Fin 20) (hv : v ∈ D) (S : Finset (Fin 20))
    (hS : ∀ s ∈ S, s ≠ v ∧ ¬ G.Adj v s) : (S \ C).card ≤ 2 :=
  boundary_four_five_blocks_even_shores_impossible_generic_bound G hdegree v C S hC (fun h => (Finset.disjoint_left.mp hCD) h hv)
    (fun c hc hadj => hnoCD c hc v hv ((G.adj_comm v c).mp hadj)) hS

theorem boundary_four_five_blocks_even_shores_impossible
    (G : SimpleGraph (Fin 20)) [DecidableRel G.Adj]
    (A B C D : Finset (Fin 20))
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (hcover : A ∪ B ∪ C ∪ D = Finset.univ)
    (hA : A.card=5) (hB : B.card=5) (hC : C.card=5) (hD : D.card=5)
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hnoCD : ∀ c ∈ C, ∀ d ∈ D, ¬ G.Adj c d)
    (hdegree : ∀ v, 12 ≤ (G.neighborFinset v).card)
    (x y : Fin 20) (hx : x ∈ A) (hy : y ∈ C)
    (Q W : Finset (Fin 20)) (hQW : Disjoint Q W)
    (hxQ : x ∉ Q) (hyQ : y ∉ Q) (hxW : x ∉ W) (hyW : y ∉ W)
    (hQeven : Even Q.card) (hWeven : Even W.card)
    (hsize : (Q ∪ W ∪ {x,y}).card = 10)
    (hyQadj : ∀ q ∈ Q, ¬ G.Adj y q)
    (hxWadj : ∀ w ∈ W, ¬ G.Adj x w)
    (hcross : ∀ q ∈ Q, ∀ w ∈ W, ¬ G.Adj q w) : False := by
  have hxy : x ≠ y := by
    rintro rfl; exact (Finset.disjoint_left.mp hAC) hx hy
  have hxQW : x ∉ Q ∪ W := by
    rw [Finset.mem_union]; rintro (h | h); exact hxQ h; exact hxW h
  have hyQW : y ∉ Q ∪ W := by
    rw [Finset.mem_union]; rintro (h | h); exact hyQ h; exact hyW h
  have hdisj_xy : Disjoint (Q ∪ W) ({x, y} : Finset (Fin 20)) := by
    rw [Finset.disjoint_left]
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (rfl | rfl)
    · exact hxQW ha
    · exact hyQW ha
  have hQW8 : Q.card + W.card = 8 := by
    have h := hsize
    rw [Finset.card_union_of_disjoint hdisj_xy, Finset.card_pair hxy,
        Finset.card_union_of_disjoint hQW] at h
    omega
  have hQeq : (Q ∩ D).card + (Q \ D).card = Q.card := Finset.card_inter_add_card_sdiff Q D
  have hWeq : (W ∩ B).card + (W \ B).card = W.card := Finset.card_inter_add_card_sdiff W B
  have hQDs : (Q \ D).card ≤ 2 := by
    refine boundary_four_five_blocks_even_shores_impossible_boundC G hdegree C D hCD hD hnoCD y hy Q ?_
    intro q hq; exact ⟨fun h => hyQ (h ▸ hq), fun h => hyQadj q hq h⟩
  have hWBs : (W \ B).card ≤ 2 := by
    refine boundary_four_five_blocks_even_shores_impossible_boundA G hdegree A B hAB hB hnoAB x hx W ?_
    intro w hw; exact ⟨fun h => hxW (h ▸ hw), fun h => hxWadj w hw h⟩
  have hQDcard : (Q ∩ D).card ≤ 5 := by
    calc (Q ∩ D).card ≤ D.card := Finset.card_le_card Finset.inter_subset_right
      _ = 5 := hD
  have hWBcard : (W ∩ B).card ≤ 5 := by
    calc (W ∩ B).card ≤ B.card := Finset.card_le_card Finset.inter_subset_right
      _ = 5 := hB
  have mem_blocks : ∀ z : Fin 20, z ∈ A ∨ z ∈ B ∨ z ∈ C ∨ z ∈ D := by
    intro z
    have h : z ∈ A ∪ B ∪ C ∪ D := by rw [hcover]; exact Finset.mem_univ z
    simp only [Finset.mem_union] at h; tauto
  have hQle7 : Q.card ≤ 7 := by omega
  have hWle7 : W.card ≤ 7 := by omega
  have hnn_WB : ∀ q : Fin 20, q ∈ Q → ∀ s ∈ W ∩ B, s ≠ q ∧ ¬ G.Adj q s := by
    intro q hq s hs
    rw [Finset.mem_inter] at hs
    exact ⟨fun h => (Finset.disjoint_left.mp hQW) hq (h ▸ hs.1), hcross q hq s hs.1⟩
  have hnn_QD : ∀ w : Fin 20, w ∈ W → ∀ s ∈ Q ∩ D, s ≠ w ∧ ¬ G.Adj w s := by
    intro w hw s hs
    rw [Finset.mem_inter] at hs
    exact ⟨fun h => (Finset.disjoint_left.mp hQW) hs.1 (h ▸ hw),
      fun h => hcross s hs.1 w hw ((G.adj_comm w s).mp h)⟩
  by_cases hQsmall : Q.card ≤ 2
  · -- ===== Case 1: Q.card ≤ 2 =====
    have hWge6 : 6 ≤ W.card := by omega
    have hbge4 : 4 ≤ (W ∩ B).card := by omega
    have hQA : Q ⊆ A := by
      intro q hq
      by_contra hqA
      rcases mem_blocks q with hA' | hB' | hC' | hD'
      · exact hqA hA'
      · refine boundary_four_five_blocks_even_shores_impossible_contraB G hdegree A B hAB hA hnoAB q hB' (W ∩ B) ?_ (hnn_WB q hq) ?_
        · omega
        · intro s hs; exact (Finset.disjoint_right.mp hAB) ((Finset.mem_inter.mp hs).2)
      · refine boundary_four_five_blocks_even_shores_impossible_contraC G hdegree C D hCD hD hnoCD q hC' (W ∩ B) ?_ (hnn_WB q hq) ?_
        · omega
        · intro s hs; exact (Finset.disjoint_left.mp hBD) ((Finset.mem_inter.mp hs).2)
      · refine boundary_four_five_blocks_even_shores_impossible_contraD G hdegree C D hCD hC hnoCD q hD' (W ∩ B) ?_ (hnn_WB q hq) ?_
        · omega
        · intro s hs; exact (Finset.disjoint_left.mp hBC) ((Finset.mem_inter.mp hs).2)
    have hQ2 : Q.card = 2 := by obtain ⟨m, hm⟩ := hQeven; omega
    have hW6 : W.card = 6 := by omega
    have hWBne : 0 < (W \ B).card := by omega
    obtain ⟨w, hw⟩ := Finset.card_pos.mp hWBne
    rw [Finset.mem_sdiff] at hw
    obtain ⟨hwW, hwB⟩ := hw
    have hTcard : 3 ≤ (({x} : Finset (Fin 20)) ∪ Q).card := by
      have hc : (({x} : Finset (Fin 20)) ∪ Q).card = 3 := by
        rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_left.mpr hxQ),
          Finset.card_singleton, hQ2]
      omega
    have hTnn : ∀ s ∈ (({x} : Finset (Fin 20)) ∪ Q), s ≠ w ∧ ¬ G.Adj w s := by
      intro s hs
      rw [Finset.mem_union, Finset.mem_singleton] at hs
      rcases hs with hEq | hsQ
      · rw [hEq]
        exact ⟨fun h => hxW (h ▸ hwW), fun h => hxWadj w hwW ((G.adj_comm w x).mp h)⟩
      · exact ⟨fun h => (Finset.disjoint_left.mp hQW) hsQ (h ▸ hwW),
               fun h => hcross s hsQ w hwW ((G.adj_comm w s).mp h)⟩
    have hTA : ∀ s ∈ (({x} : Finset (Fin 20)) ∪ Q), s ∈ A := by
      intro s hs
      rw [Finset.mem_union, Finset.mem_singleton] at hs
      rcases hs with hEq | hsQ
      · rw [hEq]; exact hx
      · exact hQA hsQ
    rcases mem_blocks w with hwA | hwB' | hwC | hwD
    · refine boundary_four_five_blocks_even_shores_impossible_contraA G hdegree A B hAB hB hnoAB w hwA (({x} : Finset (Fin 20)) ∪ Q) hTcard hTnn ?_
      intro s hs
      exact (Finset.disjoint_left.mp hAB) (hTA s hs)
    · exact absurd hwB' hwB
    · refine boundary_four_five_blocks_even_shores_impossible_contraC G hdegree C D hCD hD hnoCD w hwC (({x} : Finset (Fin 20)) ∪ Q) hTcard hTnn ?_
      intro s hs
      exact (Finset.disjoint_left.mp hAD) (hTA s hs)
    · refine boundary_four_five_blocks_even_shores_impossible_contraD G hdegree C D hCD hC hnoCD w hwD (({x} : Finset (Fin 20)) ∪ Q) hTcard hTnn ?_
      intro s hs
      exact (Finset.disjoint_left.mp hAC) (hTA s hs)
  · -- Q.card ≥ 4
    have hQge4 : 4 ≤ Q.card := by obtain ⟨m, hm⟩ := hQeven; omega
    by_cases hWsmall : W.card ≤ 2
    · -- ===== Case 2: W.card ≤ 2 =====
      have hQge6 : 6 ≤ Q.card := by omega
      have hage4 : 4 ≤ (Q ∩ D).card := by omega
      have hWC : W ⊆ C := by
        intro w hw
        by_contra hwC
        rcases mem_blocks w with hA' | hB' | hC' | hD'
        · refine boundary_four_five_blocks_even_shores_impossible_contraA G hdegree A B hAB hB hnoAB w hA' (Q ∩ D) ?_ (hnn_QD w hw) ?_
          · omega
          · intro s hs; exact (Finset.disjoint_right.mp hBD) ((Finset.mem_inter.mp hs).2)
        · refine boundary_four_five_blocks_even_shores_impossible_contraB G hdegree A B hAB hA hnoAB w hB' (Q ∩ D) ?_ (hnn_QD w hw) ?_
          · omega
          · intro s hs; exact (Finset.disjoint_right.mp hAD) ((Finset.mem_inter.mp hs).2)
        · exact hwC hC'
        · refine boundary_four_five_blocks_even_shores_impossible_contraD G hdegree C D hCD hC hnoCD w hD' (Q ∩ D) ?_ (hnn_QD w hw) ?_
          · omega
          · intro s hs; exact (Finset.disjoint_right.mp hCD) ((Finset.mem_inter.mp hs).2)
      have hW2 : W.card = 2 := by obtain ⟨m, hm⟩ := hWeven; omega
      have hQ6 : Q.card = 6 := by omega
      have hQDne : 0 < (Q \ D).card := by omega
      obtain ⟨q, hq⟩ := Finset.card_pos.mp hQDne
      rw [Finset.mem_sdiff] at hq
      obtain ⟨hqQ, hqD⟩ := hq
      have hTcard : 3 ≤ (({y} : Finset (Fin 20)) ∪ W).card := by
        have hc : (({y} : Finset (Fin 20)) ∪ W).card = 3 := by
          rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_left.mpr hyW),
            Finset.card_singleton, hW2]
        omega
      have hTnn : ∀ s ∈ (({y} : Finset (Fin 20)) ∪ W), s ≠ q ∧ ¬ G.Adj q s := by
        intro s hs
        rw [Finset.mem_union, Finset.mem_singleton] at hs
        rcases hs with hEq | hsW
        · rw [hEq]
          exact ⟨fun h => hyQ (h ▸ hqQ), fun h => hyQadj q hqQ ((G.adj_comm q y).mp h)⟩
        · exact ⟨fun h => (Finset.disjoint_left.mp hQW) hqQ (h ▸ hsW), hcross q hqQ s hsW⟩
      have hTC : ∀ s ∈ (({y} : Finset (Fin 20)) ∪ W), s ∈ C := by
        intro s hs
        rw [Finset.mem_union, Finset.mem_singleton] at hs
        rcases hs with hEq | hsW
        · rw [hEq]; exact hy
        · exact hWC hsW
      rcases mem_blocks q with hqA | hqB | hqC | hqD'
      · refine boundary_four_five_blocks_even_shores_impossible_contraA G hdegree A B hAB hB hnoAB q hqA (({y} : Finset (Fin 20)) ∪ W) hTcard hTnn ?_
        intro s hs
        exact (Finset.disjoint_right.mp hBC) (hTC s hs)
      · refine boundary_four_five_blocks_even_shores_impossible_contraB G hdegree A B hAB hA hnoAB q hqB (({y} : Finset (Fin 20)) ∪ W) hTcard hTnn ?_
        intro s hs
        exact (Finset.disjoint_right.mp hAC) (hTC s hs)
      · refine boundary_four_five_blocks_even_shores_impossible_contraC G hdegree C D hCD hD hnoCD q hqC (({y} : Finset (Fin 20)) ∪ W) hTcard hTnn ?_
        intro s hs
        exact (Finset.disjoint_left.mp hCD) (hTC s hs)
      · exact hqD hqD'
    · -- ===== Case 3: Q.card = W.card = 4 =====
      have hWge4 : 4 ≤ W.card := by obtain ⟨m, hm⟩ := hWeven; omega
      have hQ4 : Q.card = 4 := by omega
      have hW4 : W.card = 4 := by omega
      have hage2 : 2 ≤ (Q ∩ D).card := by omega
      have hbge2 : 2 ≤ (W ∩ B).card := by omega
      have ha_le2 : (Q ∩ D).card ≤ 2 := by
        obtain ⟨e, he⟩ := Finset.card_pos.mp (by omega : 0 < (W ∩ B).card)
        rw [Finset.mem_inter] at he
        obtain ⟨heW, heB⟩ := he
        have hbnd := boundary_four_five_blocks_even_shores_impossible_boundB G hdegree A B hAB hA hnoAB e heB (Q ∩ D) (hnn_QD e heW)
        have hQDA : (Q ∩ D) \ A = Q ∩ D := by
          ext s; rw [Finset.mem_sdiff, Finset.mem_inter]
          exact ⟨fun h => h.1, fun h => ⟨h, fun hA' => (Finset.disjoint_left.mp hAD) hA' h.2⟩⟩
        rwa [hQDA] at hbnd
      have hb_le2 : (W ∩ B).card ≤ 2 := by
        obtain ⟨d, hd⟩ := Finset.card_pos.mp (by omega : 0 < (Q ∩ D).card)
        rw [Finset.mem_inter] at hd
        obtain ⟨hdQ, hdD⟩ := hd
        have hbnd := boundary_four_five_blocks_even_shores_impossible_boundD G hdegree C D hCD hC hnoCD d hdD (W ∩ B) (hnn_WB d hdQ)
        have hWBC : (W ∩ B) \ C = W ∩ B := by
          ext s; rw [Finset.mem_sdiff, Finset.mem_inter]
          exact ⟨fun h => h.1, fun h => ⟨h, fun hC' => (Finset.disjoint_left.mp hBC) h.2 hC'⟩⟩
        rwa [hWBC] at hbnd
      have ha2 : (Q ∩ D).card = 2 := by omega
      have hb2 : (W ∩ B).card = 2 := by omega
      have hQDdiff2 : (Q \ D).card = 2 := by omega
      obtain ⟨w, hw⟩ := Finset.card_pos.mp (by omega : 0 < (W \ B).card)
      rw [Finset.mem_sdiff] at hw
      obtain ⟨hwW, hwB⟩ := hw
      have hxQD : x ∉ Q ∩ D := by rw [Finset.mem_inter]; rintro ⟨h, _⟩; exact hxQ h
      have hxQdiff : x ∉ Q \ D := by rw [Finset.mem_sdiff]; rintro ⟨h, _⟩; exact hxQ h
      have hT1card : 3 ≤ (({x} : Finset (Fin 20)) ∪ (Q ∩ D)).card := by
        have hc : (({x} : Finset (Fin 20)) ∪ (Q ∩ D)).card = 3 := by
          rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_left.mpr hxQD),
            Finset.card_singleton, ha2]
        omega
      have hT2card : 3 ≤ (({x} : Finset (Fin 20)) ∪ (Q \ D)).card := by
        have hc : (({x} : Finset (Fin 20)) ∪ (Q \ D)).card = 3 := by
          rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_left.mpr hxQdiff),
            Finset.card_singleton, hQDdiff2]
        omega
      have hT1nn : ∀ s ∈ (({x} : Finset (Fin 20)) ∪ (Q ∩ D)), s ≠ w ∧ ¬ G.Adj w s := by
        intro s hs
        rw [Finset.mem_union, Finset.mem_singleton] at hs
        rcases hs with hEq | hs
        · rw [hEq]
          exact ⟨fun h => hxW (h ▸ hwW), fun h => hxWadj w hwW ((G.adj_comm w x).mp h)⟩
        · rw [Finset.mem_inter] at hs
          exact ⟨fun h => (Finset.disjoint_left.mp hQW) hs.1 (h ▸ hwW),
            fun h => hcross s hs.1 w hwW ((G.adj_comm w s).mp h)⟩
      have hT2nn : ∀ s ∈ (({x} : Finset (Fin 20)) ∪ (Q \ D)), s ≠ w ∧ ¬ G.Adj w s := by
        intro s hs
        rw [Finset.mem_union, Finset.mem_singleton] at hs
        rcases hs with hEq | hs
        · rw [hEq]
          exact ⟨fun h => hxW (h ▸ hwW), fun h => hxWadj w hwW ((G.adj_comm w x).mp h)⟩
        · rw [Finset.mem_sdiff] at hs
          exact ⟨fun h => (Finset.disjoint_left.mp hQW) hs.1 (h ▸ hwW),
            fun h => hcross s hs.1 w hwW ((G.adj_comm w s).mp h)⟩
      rcases mem_blocks w with hwA | hwB' | hwC | hwD
      · refine boundary_four_five_blocks_even_shores_impossible_contraA G hdegree A B hAB hB hnoAB w hwA (({x} : Finset (Fin 20)) ∪ (Q ∩ D)) hT1card hT1nn ?_
        intro s hs
        rw [Finset.mem_union, Finset.mem_singleton] at hs
        rcases hs with hEq | hs
        · rw [hEq]; exact (Finset.disjoint_left.mp hAB) hx
        · rw [Finset.mem_inter] at hs; exact (Finset.disjoint_right.mp hBD) hs.2
      · exact absurd hwB' hwB
      · refine boundary_four_five_blocks_even_shores_impossible_contraC G hdegree C D hCD hD hnoCD w hwC (({x} : Finset (Fin 20)) ∪ (Q \ D)) hT2card hT2nn ?_
        intro s hs
        rw [Finset.mem_union, Finset.mem_singleton] at hs
        rcases hs with hEq | hs
        · rw [hEq]; exact (Finset.disjoint_left.mp hAD) hx
        · rw [Finset.mem_sdiff] at hs; exact hs.2
      · refine boundary_four_five_blocks_even_shores_impossible_contraD G hdegree C D hCD hC hnoCD w hwD (({x} : Finset (Fin 20)) ∪ (Q ∩ D)) hT1card hT1nn ?_
        intro s hs
        rw [Finset.mem_union, Finset.mem_singleton] at hs
        rcases hs with hEq | hs
        · rw [hEq]; exact (Finset.disjoint_left.mp hAC) hx
        · rw [Finset.mem_inter] at hs; exact (Finset.disjoint_right.mp hCD) hs.2
