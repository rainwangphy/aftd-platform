import AFTD.Prelude
import AFTD.Kb.Tcs.ExternalNeighborCountAtMostDegreeSubThree
import AFTD.Kb.Tcs.ExternalNeighborCountWithRInternal
import AFTD.Kb.Tcs.ChooseExternalNonNeighborPadding

/-!
# bridge_family_variable_refined_walk_budget

Topic: graphs   Node: ecb3d691aca8

Provenance: helper lemma. OP-1957 variable-shore bridge-family incidence and padded-walk count.

A bridge family with shores of size at least r has at least r(r−3)|T| missing padded walks.
-/

theorem bridge_family_variable_refined_walk_budget {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x y : V) (hxy : x ≠ y)
    (S C : Finset V) (d L r : ℕ) (hr : 4 ≤ r) (hCr : d ≤ C.card) (hSC : Disjoint S C) (hxC : x ∉ C) (hyC : y ∉ C)
    (hSsize : S.card+1=d) (hmax : ∀ a, (H.neighborFinset a).card ≤ d)
    (hSxy : ∀ w ∈ S, H.Adj w x ∧ H.Adj w y) (Q W : V → Finset V)
    (hdis : ∀ z ∈ C, Disjoint (Q z) (W z))
    (hQ : ∀ z ∈ C, Q z ⊆ S ∪ C) (hW : ∀ z ∈ C, W z ⊆ S)
    (hsize : ∀ z ∈ C, (Q z).card+(W z).card=d+1)
    (hxQ : ∀ z ∈ C, x ∉ Q z) (hyQ : ∀ z ∈ C, y ∉ Q z)
    (hzQ : ∀ z ∈ C, ∀ q ∈ Q z, H.Adj z q)
    (hcross : ∀ z ∈ C, ∀ q ∈ Q z, ∀ w ∈ W z, H.Adj q w)
    (hWmin : ∀ z ∈ C, r ≤ (W z).card)
    (hprod : ∀ z ∈ C, L ≤ (W z).card * (Q z).card) :
    let T := C.filter (fun q => r ≤ ((H.neighborFinset q) ∩ S).card)
    L * C.card + r*(r-3)*T.card ≤ (d-1)*(d-2)*(d-3) := by
  classical
  let T := C.filter (fun q => r ≤ ((H.neighborFinset q) ∩ S).card)
  have hpads : ∀ q : V, ∃ P : Finset V, q ∈ T →
      P ⊆ C \ H.neighborFinset q ∧ P.card = r-3 := by
    intro q
    by_cases hq : q ∈ T
    · have hqin := (Finset.mem_filter.mp hq).2
      obtain ⟨P,hsub,hcard⟩ := choose_external_non_neighbor_padding H q S C d r hSC hr hCr (hmax q) hqin
      exact ⟨P,fun _ => ⟨hsub,hcard⟩⟩
    · exact ⟨∅,fun h => (hq h).elim⟩
  choose Pad hPad using hpads
  let Z : V → Finset V := fun q => if q ∈ T then ((H.neighborFinset q) ∩ C) ∪ Pad q else ((H.neighborFinset q) ∩ C)
  let D : V → Finset V := fun w => (((H.neighborFinset w).erase x).erase y).filter
    (fun q => q ∈ S ∨ q ∈ T)
  let upper : Finset ((V × V) × V) := S.biUnion fun w =>
    (D w).biUnion fun q => (Z q).image (fun z => ((w,q),z))
  have hupper : upper.card ≤ S.card * ((d-2)*(d-3)) := by
    dsimp [upper]
    apply Finset.card_biUnion_le_card_mul
    intro w hw
    have hx : x ∈ H.neighborFinset w := by simpa using (hSxy w hw).1
    have hy : y ∈ (H.neighborFinset w).erase x := by
      apply Finset.mem_erase.mpr
      exact ⟨hxy.symm, by simpa using (hSxy w hw).2⟩
    have hwcard : (D w).card ≤ d-2 := by
      have hfilter : (D w).card ≤ (((H.neighborFinset w).erase x).erase y).card := by
        exact Finset.card_le_card (Finset.filter_subset _ _)
      rw [Finset.card_erase_of_mem hy,Finset.card_erase_of_mem hx] at hfilter
      have hm := hmax w
      have hxcard : 2 ≤ (H.neighborFinset w).card := by
        have hpair : ({x,y} : Finset V) ⊆ H.neighborFinset w := by
          intro a ha
          simp only [Finset.mem_insert,Finset.mem_singleton] at ha
          rcases ha with rfl | rfl
          · exact hx
          · exact Finset.mem_of_mem_erase hy
        have hc := Finset.card_le_card hpair
        rw [Finset.card_pair hxy] at hc
        exact hc
      omega
    have hinner : ∀ q ∈ D w, ((Z q).image (fun z => ((w,q),z))).card ≤ d-3 := by
      intro q hq
      have hq' := Finset.mem_filter.mp hq
      have hqN := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hq'.1)
      have hqw : H.Adj q w := by
        have h : H.Adj w q := by simpa using hqN
        exact h.symm
      have hZ : (Z q).card ≤ d-3 := by
        by_cases hqT : q ∈ T
        · have hqin := (Finset.mem_filter.mp hqT).2
          have hc := external_neighbor_count_with_r_internal H q S C d r hSC (hmax q) hqin
          obtain ⟨hpsub,hpcard⟩ := hPad q hqT
          have hd : Disjoint ((H.neighborFinset q) ∩ C) (Pad q) := by
            apply Finset.disjoint_left.mpr
            intro a ha hp
            have hp' := hpsub hp
            exact (Finset.mem_sdiff.mp hp').2 (Finset.mem_inter.mp ha).1
          dsimp [Z]
          rw [if_pos hqT,Finset.card_union_of_disjoint hd,hpcard]
          omega
        · have hqS : q ∈ S := by
            rcases hq'.2 with hs | ht
            · exact hs
            · exact (hqT ht).elim
          have hqtype : q ∈ S ∨ (q ∈ C ∧ 3 ≤ ((H.neighborFinset q) ∩ S).card) := Or.inl hqS
          have hc := external_neighbor_count_at_most_degree_sub_three H x y w q hxy S C d hSC hxC hyC hw hSxy hqw (hmax q) hqtype
          simpa [Z,hqT] using hc
      exact le_trans Finset.card_image_le hZ
    have hc := Finset.card_biUnion_le_card_mul (D w)
      (fun q => (Z q).image (fun z => ((w,q),z))) (d-3) hinner
    exact le_trans hc (Nat.mul_le_mul_right (d-3) hwcard)
  let lower : Finset ((V × V) × V) := C.biUnion fun z =>
    ((W z) ×ˢ (Q z)).image (fun p => ((p.1,p.2),z))
  have hitem : ∀ z, (((W z) ×ˢ (Q z)).image (fun p => ((p.1,p.2),z))).card =
      (W z).card*(Q z).card := by
    intro z
    rw [Finset.card_image_of_injective _ (by intro a b h; exact congrArg Prod.fst h),Finset.card_product]
  have hpairwise : (C : Set V).PairwiseDisjoint (fun z =>
      ((W z) ×ˢ (Q z)).image (fun p => ((p.1,p.2),z))) := by
    intro z hz z' hz' hne
    apply Finset.disjoint_left.mpr
    intro t ht ht'
    obtain ⟨p,hp,he⟩ := Finset.mem_image.mp ht
    obtain ⟨p',hp',he'⟩ := Finset.mem_image.mp ht'
    apply hne
    exact (congrArg Prod.snd he).trans (congrArg Prod.snd he').symm
  have hlower : L * C.card ≤ lower.card := by
    dsimp [lower]
    rw [Finset.card_biUnion hpairwise]
    have hs : ∑ z ∈ C, L ≤ ∑ z ∈ C, (W z).card*(Q z).card := by
      apply Finset.sum_le_sum
      intro z hz
      exact hprod z hz
    simp only [hitem] at *
    simpa [Nat.mul_comm] using hs
  have hsub : lower ⊆ upper := by
    intro t ht
    obtain ⟨z,hz,ht⟩ := Finset.mem_biUnion.mp ht
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hw,hq⟩ := Finset.mem_product.mp hp
    have hwS : p.1 ∈ S := hW z hz hw
    have hqN : p.2 ∈ H.neighborFinset p.1 := by simpa using (hcross z hz p.2 hq p.1 hw).symm
    have hqx : p.2 ≠ x := fun he => hxQ z hz (he ▸ hq)
    have hqy : p.2 ≠ y := fun he => hyQ z hz (he ▸ hq)
    have hqgood : p.2 ∈ S ∨ p.2 ∈ T := by
      rcases Finset.mem_union.mp (hQ z hz hq) with hs | hc
      · exact Or.inl hs
      · right
        apply Finset.mem_filter.mpr
        refine ⟨hc, ?_⟩
        have hsub : W z ⊆ (H.neighborFinset p.2) ∩ S := by
          intro w hw'
          apply Finset.mem_inter.mpr
          exact ⟨by simpa using hcross z hz p.2 hq w hw', hW z hz hw'⟩
        have hle := Finset.card_le_card hsub
        have hm := hWmin z hz
        omega
    have hq' : p.2 ∈ D p.1 := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_erase.mpr ⟨hqy,Finset.mem_erase.mpr ⟨hqx,hqN⟩⟩, hqgood⟩
    have hzN : z ∈ H.neighborFinset p.2 := by simpa using (hzQ z hz p.2 hq).symm
    apply Finset.mem_biUnion.mpr
    refine ⟨p.1,hwS,Finset.mem_biUnion.mpr ⟨p.2,hq',?_⟩⟩
    apply Finset.mem_image.mpr
    refine ⟨z, ?_, rfl⟩
    by_cases hpT : p.2 ∈ T
    · simp only [Z,if_pos hpT,Finset.mem_union]
      exact Or.inl (Finset.mem_inter.mpr ⟨hzN,hz⟩)
    · simp only [Z,if_neg hpT]
      exact Finset.mem_inter.mpr ⟨hzN,hz⟩
  let extra : Finset ((V × V) × V) := T.biUnion fun q =>
    (((H.neighborFinset q) ∩ S) ×ˢ Pad q).image (fun p => ((p.1,q),p.2))
  have heItem : ∀ q, ((((H.neighborFinset q) ∩ S) ×ˢ Pad q).image (fun p => ((p.1,q),p.2))).card =
      ((H.neighborFinset q) ∩ S).card*(Pad q).card := by
    intro q
    rw [Finset.card_image_of_injective _ (by intro a b h; cases a; cases b; simp_all), Finset.card_product]
  have hePair : (T : Set V).PairwiseDisjoint (fun q =>
      (((H.neighborFinset q) ∩ S) ×ˢ Pad q).image (fun p => ((p.1,q),p.2))) := by
    intro q hq q' hq' hne
    apply Finset.disjoint_left.mpr
    intro t ht ht'
    obtain ⟨a,ha,he⟩ := Finset.mem_image.mp ht
    obtain ⟨b,hb,he'⟩ := Finset.mem_image.mp ht'
    apply hne
    exact (congrArg (fun t : (V × V) × V => t.1.2) he).trans (congrArg (fun t : (V × V) × V => t.1.2) he').symm
  have hextra : r*(r-3)*T.card ≤ extra.card := by
    dsimp [extra]
    rw [Finset.card_biUnion hePair]
    have hs : ∑ q ∈ T, r*(r-3) ≤ ∑ q ∈ T, ((H.neighborFinset q) ∩ S).card*(Pad q).card := by
      apply Finset.sum_le_sum
      intro q hq
      have hqin := (Finset.mem_filter.mp hq).2
      have hp := (hPad q hq).2
      rw [hp]
      exact Nat.mul_le_mul_right (r-3) hqin
    simp only [heItem] at *
    simpa [Nat.mul_comm,Nat.mul_assoc,Nat.mul_left_comm] using hs
  have hextraSub : extra ⊆ upper := by
    intro t ht
    obtain ⟨q,hqT,ht⟩ := Finset.mem_biUnion.mp ht
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨hw,hz⟩ := Finset.mem_product.mp hp
    have hqC : q ∈ C := (Finset.mem_filter.mp hqT).1
    have hwS : p.1 ∈ S := (Finset.mem_inter.mp hw).2
    have hqw : H.Adj q p.1 := by simpa using (Finset.mem_inter.mp hw).1
    have hqN : q ∈ H.neighborFinset p.1 := by simpa using hqw.symm
    have hqx : q ≠ x := fun h => hxC (h ▸ hqC)
    have hqy : q ≠ y := fun h => hyC (h ▸ hqC)
    have hqD : q ∈ D p.1 := Finset.mem_filter.mpr
      ⟨Finset.mem_erase.mpr ⟨hqy,Finset.mem_erase.mpr ⟨hqx,hqN⟩⟩, Or.inr hqT⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨p.1,hwS,Finset.mem_biUnion.mpr ⟨q,hqD,?_⟩⟩
    apply Finset.mem_image.mpr
    refine ⟨p.2, ?_, rfl⟩
    simp only [Z,if_pos hqT,Finset.mem_union]
    exact Or.inr hz
  have hdisjoint : Disjoint lower extra := by
    apply Finset.disjoint_left.mpr
    intro t ht ht'
    obtain ⟨q,hqT,ht'⟩ := Finset.mem_biUnion.mp ht'
    obtain ⟨p,hp,he⟩ := Finset.mem_image.mp ht'
    obtain ⟨z,hz,ht⟩ := Finset.mem_biUnion.mp ht
    obtain ⟨p',hp',he'⟩ := Finset.mem_image.mp ht
    have hpq : p'.2 = q := congrArg (fun t : (V × V) × V => t.1.2) (he'.trans he.symm)
    have hzp : z = p.2 := congrArg Prod.snd (he'.trans he.symm)
    have hpQ : p'.2 ∈ Q z := (Finset.mem_product.mp hp').2
    have hh := hzQ z hz p'.2 hpQ
    rw [hpq,hzp] at hh
    have hzPad : p.2 ∈ Pad q := (Finset.mem_product.mp hp).2
    have hzNot : p.2 ∉ H.neighborFinset q := (Finset.mem_sdiff.mp ((hPad q hqT).1 hzPad)).2
    exact hzNot (by simpa using hh.symm)
  have hunion : lower ∪ extra ⊆ upper := Finset.union_subset hsub hextraSub
  have hcount := Finset.card_le_card hunion
  rw [Finset.card_union_of_disjoint hdisjoint] at hcount
  have hbound : L*C.card + r*(r-3)*T.card ≤ S.card*((d-2)*(d-3)) := by
    have := hupper
    omega
  have hS : S.card = d-1 := by omega
  rw [hS] at hbound
  simpa [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hbound
