import AFTD.Prelude
import AFTD.Kb.Tcs.OddGroupsBudgetAfterForcedMatching

/-!
# four_odd_groups_star_forced_matching_obstruction

Topic: graphs   Node: 18b21c67dc5b

Provenance: helper lemma. Balanced-cut k=7 reduction for OP-1957; https://arxiv.org/abs/2611.22690.

Under the displayed four-group star conditions, a partial matching forcing the center and leaving at most five vertices on the other side cannot extend to a perfect matching.
-/

theorem four_odd_groups_star_forced_matching_obstruction
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (C : Finset V) (F : Fin 4 → Finset V)
    (hsub : ∀ i, F i ⊆ Cᶜ)
    (hodd : ∀ i, Odd (F i).card)
    (hdis : ∀ i j, i ≠ j → Disjoint (F i) (F j))
    (hanti : ∀ i j, i ≠ j → ∀ u ∈ F i, ∀ v ∈ F j, ¬ G.Adj u v)
    (hcover : Finset.univ.biUnion F = Cᶜ)
    (z : Fin 4) (x : V) (hx : x ∈ F z) (hzcard : (F z).card=5)
    (hstar : ∀ u ∈ F z, ∀ v ∈ F z, G.Adj u v → u=x ∨ v=x)
    (P T : G.Subgraph) (hP : P.IsPerfectMatching) (hT : T.IsMatching) (hTP : T ≤ P)
    (hxT : x ∈ T.verts) (hTsub : T.verts ⊆ ((C ∪ {x} : Finset V) : Set V))
    (hremain : ((C : Set V) \ T.verts).ncard ≤ 5) : False := by
  set_option maxHeartbeats 4000000 in
    classical
    let JL : Finset (Fin 4) := Finset.univ.erase z
    let JR : Finset V := (F z).erase x
    let J : Finset (Fin 4 ⊕ V) := JL.disjSum JR
    let B : Fin 4 ⊕ V → Finset V := Sum.elim F (fun v => {v})
    let L : Finset V := Cᶜ \ {x}
    have hleft : ∀ i, Sum.inl i ∈ J ↔ i ≠ z := by intro i; simp [J,JL]
    have hright : ∀ v, Sum.inr v ∈ J ↔ v ≠ x ∧ v ∈ F z := by intro v; simp [J,JR]
    have hJcard : J.card = 7 := by
      have hl := Finset.card_erase_add_one (Finset.mem_univ z)
      have hr := Finset.card_erase_add_one hx
      simp only [Finset.card_univ,Fintype.card_fin] at hl
      dsimp [J,JL,JR]
      rw [Finset.card_disjSum]
      omega
    have hJsub : ∀ i ∈ J, B i ⊆ L := by
      intro i hi
      cases i with
      | inl j =>
        have hj : j ≠ z := (hleft j).mp hi
        intro v hv
        have hvF : v ∈ F j := hv
        have hvC : v ∈ Cᶜ := hsub j hvF
        have hvx : v ≠ x := by
          intro he
          exact Finset.disjoint_left.mp (hdis j z hj) hvF (he.symm ▸ hx)
        exact Finset.mem_sdiff.mpr ⟨hvC,by simpa using hvx⟩
      | inr v =>
        have hv := (hright v).mp hi
        intro w hw
        have he : w=v := by simpa [B] using hw
        subst w
        exact Finset.mem_sdiff.mpr ⟨hsub z hv.2,by simpa using hv.1⟩
    have hJodd : ∀ i ∈ J, Odd (B i).card := by
      intro i hi
      cases i with
      | inl j => exact hodd j
      | inr v => simp [B]
    have hJdis : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (B i) (B j) := by
      intro i hi j hj hij
      cases i with
      | inl a =>
        cases j with
        | inl b => exact hdis a b (by intro h; apply hij; simp [h])
        | inr b =>
          have ha := (hleft a).mp hi
          have hb := (hright b).mp hj
          apply Finset.disjoint_left.mpr
          intro v hva hvb
          have he : v=b := by simpa [B] using hvb
          exact Finset.disjoint_left.mp (hdis a z ha) hva (he.symm ▸ hb.2)
      | inr a =>
        cases j with
        | inl b =>
          have ha := (hright a).mp hi
          have hb := (hleft b).mp hj
          apply Finset.disjoint_left.mpr
          intro v hva hvb
          have he : v=a := by simpa [B] using hva
          exact Finset.disjoint_left.mp (hdis b z hb) hvb (he.symm ▸ ha.2)
        | inr b =>
          have hab : a ≠ b := by intro h; apply hij; simp [h]
          simpa [B] using hab
    have hJanti : ∀ i ∈ J, ∀ u ∈ B i, ∀ v ∈ L, v ∉ B i → ¬ G.Adj u v := by
      intro i hi u hu v hv hvnot hadj
      have hvC : v ∈ Cᶜ := (Finset.mem_sdiff.mp hv).1
      have hvx : v ≠ x := by simpa using (Finset.mem_sdiff.mp hv).2
      have hvcover : v ∈ Finset.univ.biUnion F := by rw [hcover]; exact hvC
      obtain ⟨j,_,hvj⟩ := Finset.mem_biUnion.mp hvcover
      cases i with
      | inl a =>
        have huF : u ∈ F a := hu
        have haj : a ≠ j := by intro he; apply hvnot; simpa [B,he] using hvj
        exact hanti a j haj u huF v hvj hadj
      | inr a =>
        have ha := (hright a).mp hi
        have hua : u=a := by simpa [B] using hu
        subst u
        by_cases hj : j=z
        · subst j
          have hh := hstar a ha.2 v hvj hadj
          rcases hh with hh | hh
          · exact ha.1 hh
          · exact hvx hh
        · exact hanti z j (Ne.symm hj) a ha.2 v hvj hadj
    have hJfree : ∀ i ∈ J, ∀ u ∈ B i, u ∉ T.verts := by
      intro i hi u hu huT
      have huL := hJsub i hi hu
      have huCX := hTsub huT
      rcases Finset.mem_union.mp huCX with huC | hux
      · exact (Finset.mem_compl.mp (Finset.mem_sdiff.mp huL).1) huC
      · have hu' : u=x := by simpa using hux
        exact (Finset.mem_sdiff.mp huL).2 (by simpa [hu'])
    have hbudget := odd_groups_budget_after_forced_matching G P T hP hT hTP J B L
      hJsub hJodd hJdis hJanti hJfree
    have hcount : ((Finset.univ \ L).filter (fun v => v ∉ T.verts)).card = ((C : Set V) \ T.verts).ncard := by
      have heq : (((Finset.univ \ L).filter (fun v => v ∉ T.verts)) : Set V) =
          (C : Set V) \ T.verts := by
        ext v
        by_cases ht : v ∈ T.verts
        · simp [ht]
        · have hne : v ≠ x := fun he => ht (he.symm ▸ hxT)
          simp [L,ht,hne]
      rw [← Set.ncard_coe_finset,heq]
    rw [hJcard,hcount] at hbudget
    omega
