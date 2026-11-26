import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable

/-!
# six_class_cut_elimination

Topic: graphs   Node: 217ed0ca89e4

Provenance: helper lemma. Separator arithmetic for OP-1957; https://arxiv.org/abs/1011.3384.

In the displayed balanced six-class partition, the separator, degree and anticompleteness conditions force all vertices into the two designated classes.
-/

theorem six_class_cut_elimination
    (k : ℕ) (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (hsep : ∀ S P Q : Finset (Fin (4*k)), P.Nonempty → Q.Nonempty →
      Disjoint S P → Disjoint S Q → Disjoint P Q → S ∪ P ∪ Q = Finset.univ →
      (∀ u ∈ P, ∀ v ∈ Q, ¬ G.Adj u v) → 2*k ≤ S.card)
    (f : Fin (4*k) → Fin 6)
    (hside : ((Finset.univ : Finset (Fin (4*k))).filter (fun v => f v < 3)).card = 2*k)
    (hd1 : ∃ v, f v = 0) (hd2 : ∃ v, f v = 3)
    (hanti : ∀ u v, G.Adj u v →
      ¬ ((f u = 0 ∧ (f v = 2 ∨ f v = 4 ∨ f v = 5)) ∨
         (f u = 3 ∧ (f v = 1 ∨ f v = 2 ∨ f v = 5))))
    (hind : ∀ u v, G.Adj u v → ¬ ((f u = 1 ∧ f v = 1) ∨ (f u = 4 ∧ f v = 4)))
    (hdeg : ∀ v, 2*k+1 ≤ (G.neighborFinset v).card) :
    ∀ v, f v = 0 ∨ f v = 3 := by
  set_option maxHeartbeats 4000000 in
    classical
    let B : Fin 6 → Finset (Fin (4*k)) := fun i => Finset.univ.filter (fun v => f v = i)
    have hB : ∀ i v, v ∈ B i ↔ f v = i := by intro i v; simp [B]
    have hdis : ∀ i j, i ≠ j → Disjoint (B i) (B j) := by
      intro i j hij
      apply Finset.disjoint_left.mpr
      intro v hv hw
      exact hij ((hB i v).mp hv |>.symm.trans ((hB j v).mp hw))
    have hside' : (B 0).card + (B 1).card + (B 2).card = 2*k := by
      have hs : B 0 ∪ B 1 ∪ B 2 = Finset.univ.filter (fun v => f v < 3) := by
        ext v
        simp only [Finset.mem_union,hB,Finset.mem_filter,Finset.mem_univ,true_and]
        generalize f v = t
        fin_cases t <;> decide
      have hd01 : Disjoint (B 0) (B 1) := hdis 0 1 (by decide)
      have hd012 : Disjoint (B 0 ∪ B 1) (B 2) := Finset.disjoint_union_left.mpr ⟨hdis 0 2 (by decide), hdis 1 2 (by decide)⟩
      have hc := congrArg Finset.card hs
      rw [Finset.card_union_of_disjoint hd012, Finset.card_union_of_disjoint hd01,hside] at hc
      exact hc
    have hside2 : (B 3).card + (B 4).card + (B 5).card = 2*k := by
      have hs : B 3 ∪ B 4 ∪ B 5 = (Finset.univ.filter (fun v => f v < 3))ᶜ := by
        ext v
        simp only [Finset.mem_union,hB,Finset.mem_compl,Finset.mem_filter,Finset.mem_univ,true_and]
        generalize f v = t
        fin_cases t <;> decide
      have hd34 : Disjoint (B 3) (B 4) := hdis 3 4 (by decide)
      have hd345 : Disjoint (B 3 ∪ B 4) (B 5) := Finset.disjoint_union_left.mpr ⟨hdis 3 5 (by decide), hdis 4 5 (by decide)⟩
      have hc := congrArg Finset.card hs
      rw [Finset.card_union_of_disjoint hd345, Finset.card_union_of_disjoint hd34,Finset.card_compl,hside] at hc
      simp only [Fintype.card_fin] at hc
      omega
    have cut1 : (B 1 ∪ B 2).Nonempty → 2*k ≤ (B 0).card + (B 4).card := by
      intro hne
      let S := B 0 ∪ B 4
      let P := B 3
      let Q := (S ∪ P)ᶜ
      have hp : P.Nonempty := by obtain ⟨v,hv⟩ := hd2; exact ⟨v,(hB 3 v).mpr hv⟩
      have hq : Q.Nonempty := by
        obtain ⟨v,hv⟩ := hne
        refine ⟨v,?_⟩
        simp only [Finset.mem_union,hB] at hv
        simp only [Q,S,P,Finset.mem_compl,Finset.mem_union,hB]
        rcases hv with hv | hv <;> simp [hv]
      have hsp : Disjoint S P := Finset.disjoint_union_left.mpr ⟨hdis 0 3 (by decide),hdis 4 3 (by decide)⟩
      have hsq : Disjoint S Q := by apply Finset.disjoint_left.mpr; intro v hv hw; exact (Finset.mem_compl.mp hw) (Finset.mem_union_left P hv)
      have hpq : Disjoint P Q := by apply Finset.disjoint_left.mpr; intro v hv hw; exact (Finset.mem_compl.mp hw) (Finset.mem_union_right S hv)
      have huniv : S ∪ P ∪ Q = Finset.univ := by ext v; simp only [Q,Finset.mem_union,Finset.mem_compl,Finset.mem_univ, iff_true]; tauto
      have ha : ∀ u ∈ P, ∀ v ∈ Q, ¬ G.Adj u v := by
        intro u hu v hv hadj
        have hu' : f u = 3 := (hB 3 u).mp hu
        have hv' : f v ≠ 0 ∧ f v ≠ 4 ∧ f v ≠ 3 := by simpa [Q,S,P,hB] using hv
        have hc := hanti u v hadj
        generalize hfv : f v = t at *
        fin_cases t <;> simp_all
      have hh := hsep S P Q hp hq hsp hsq hpq huniv ha
      exact le_trans hh (Finset.card_union_le _ _)
    have cut2 : (B 4 ∪ B 5).Nonempty → 2*k ≤ (B 3).card + (B 1).card := by
      intro hne
      let S := B 3 ∪ B 1
      let P := B 0
      let Q := (S ∪ P)ᶜ
      have hp : P.Nonempty := by obtain ⟨v,hv⟩ := hd1; exact ⟨v,(hB 0 v).mpr hv⟩
      have hq : Q.Nonempty := by
        obtain ⟨v,hv⟩ := hne
        refine ⟨v,?_⟩
        simp only [Finset.mem_union,hB] at hv
        simp only [Q,S,P,Finset.mem_compl,Finset.mem_union,hB]
        rcases hv with hv | hv <;> simp [hv]
      have hsp : Disjoint S P := Finset.disjoint_union_left.mpr ⟨hdis 3 0 (by decide),hdis 1 0 (by decide)⟩
      have hsq : Disjoint S Q := by apply Finset.disjoint_left.mpr; intro v hv hw; exact (Finset.mem_compl.mp hw) (Finset.mem_union_left P hv)
      have hpq : Disjoint P Q := by apply Finset.disjoint_left.mpr; intro v hv hw; exact (Finset.mem_compl.mp hw) (Finset.mem_union_right S hv)
      have huniv : S ∪ P ∪ Q = Finset.univ := by ext v; simp only [Q,Finset.mem_union,Finset.mem_compl,Finset.mem_univ, iff_true]; tauto
      have ha : ∀ u ∈ P, ∀ v ∈ Q, ¬ G.Adj u v := by
        intro u hu v hv hadj
        have hu' : f u = 0 := (hB 0 u).mp hu
        have hv' : f v ≠ 3 ∧ f v ≠ 1 ∧ f v ≠ 0 := by simpa [Q,S,P,hB] using hv
        have hc := hanti u v hadj
        generalize hfv : f v = t at *
        fin_cases t <;> simp_all
      have hh := hsep S P Q hp hq hsp hsq hpq huniv ha
      exact le_trans hh (Finset.card_union_le _ _)
    have pos1 : (B 1 ∪ B 2).Nonempty → 0 < (B 1).card + (B 2).card := by
      intro hh
      have hpos := Finset.card_pos.mpr hh
      have hle := Finset.card_union_le (B 1) (B 2)
      omega
    have pos2 : (B 4 ∪ B 5).Nonempty → 0 < (B 4).card + (B 5).card := by
      intro hh
      have hpos := Finset.card_pos.mpr hh
      have hle := Finset.card_union_le (B 4) (B 5)
      omega
    have zero1 : ¬ (B 1 ∪ B 2).Nonempty → (B 1).card = 0 ∧ (B 2).card = 0 := by
      intro hh
      have he := Finset.not_nonempty_iff_eq_empty.mp hh
      have hc := congrArg Finset.card he
      rw [Finset.card_union_of_disjoint (hdis 1 2 (by decide)),Finset.card_empty] at hc
      omega
    have zero2 : ¬ (B 4 ∪ B 5).Nonempty → (B 4).card = 0 ∧ (B 5).card = 0 := by
      intro hh
      have he := Finset.not_nonempty_iff_eq_empty.mp hh
      have hc := congrArg Finset.card he
      rw [Finset.card_union_of_disjoint (hdis 4 5 (by decide)),Finset.card_empty] at hc
      omega
    have none1 : ¬ (B 1 ∪ B 2).Nonempty := by
      intro hh1
      have hh2 : (B 4 ∪ B 5).Nonempty := by
        by_contra hh
        have hz := zero2 hh
        have hp := pos1 hh1
        have hc := cut1 hh1
        omega
      have hp1 := pos1 hh1
      have hp2 := pos2 hh2
      have hc1 := cut1 hh1
      have hc2 := cut2 hh2
      have hz2 : (B 2).card = 0 := by omega
      have hz5 : (B 5).card = 0 := by omega
      have hB1 : (B 1).Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨u,hu⟩ := hB1
      have hu1 : f u = 1 := (hB 1 u).mp hu
      have hsub : G.neighborFinset u ⊆ B 0 ∪ B 4 := by
        intro v hv
        have huv : G.Adj u v := by simpa using hv
        have hz2' : f v ≠ 2 := by
          intro h
          have hh : v ∈ B 2 := (hB 2 v).mpr h
          have hp := Finset.card_pos.mpr ⟨v,hh⟩
          omega
        have hz5' : f v ≠ 5 := by
          intro h
          have hh : v ∈ B 5 := (hB 5 v).mpr h
          have hp := Finset.card_pos.mpr ⟨v,hh⟩
          omega
        have hi := hind u v huv
        have ha := hanti v u huv.symm
        simp only [Finset.mem_union,hB]
        generalize hfv : f v = t at *
        fin_cases t <;> simp_all
      have hc := Finset.card_le_card hsub
      have hu := Finset.card_union_le (B 0) (B 4)
      have hd := hdeg u
      omega
    have none2 : ¬ (B 4 ∪ B 5).Nonempty := by
      intro hh2
      have hz := zero1 none1
      have hp := pos2 hh2
      have hc := cut2 hh2
      omega
    intro v
    by_contra hh
    push Not at hh
    have hz1 := zero1 none1
    have hz2 := zero2 none2
    have hnot1 : f v ≠ 1 := by intro h; have hp := Finset.card_pos.mpr ⟨v,(hB 1 v).mpr h⟩; omega
    have hnot2 : f v ≠ 2 := by intro h; have hp := Finset.card_pos.mpr ⟨v,(hB 2 v).mpr h⟩; omega
    have hnot4 : f v ≠ 4 := by intro h; have hp := Finset.card_pos.mpr ⟨v,(hB 4 v).mpr h⟩; omega
    have hnot5 : f v ≠ 5 := by intro h; have hp := Finset.card_pos.mpr ⟨v,(hB 5 v).mpr h⟩; omega
    generalize hfv : f v = t at *
    fin_cases t <;> simp_all
