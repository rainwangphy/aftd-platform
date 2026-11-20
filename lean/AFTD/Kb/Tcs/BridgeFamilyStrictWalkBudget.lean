import AFTD.Prelude
import AFTD.Kb.Tcs.BridgeOppositeShoreHasTwoExternalVertices
import AFTD.Kb.Tcs.ExternalNeighborCountAtMostDegreeSubThree
import AFTD.Kb.Tcs.ExternalNeighborCountWithFourInternal

/-!
# bridge_family_strict_walk_budget

Topic: graphs   Node: 076845a16734

Provenance: helper lemma. OP-1957 simultaneous saturated-twin bridge family, without the first zero-codegree witness.

A nonempty bridge family has strictly fewer than (d−1)(d−2)(d−3) relevant complement three-walks.
-/

theorem bridge_family_strict_walk_budget {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (x y : V) (hxy : x ≠ y)
    (S C : Finset V) (d L : ℕ) (hC : C.Nonempty) (hSC : Disjoint S C) (hxC : x ∉ C) (hyC : y ∉ C)
    (hSsize : S.card+1=d) (hmax : ∀ a, (H.neighborFinset a).card ≤ d)
    (hSxy : ∀ w ∈ S, H.Adj w x ∧ H.Adj w y) (Q W : V → Finset V)
    (hdis : ∀ z ∈ C, Disjoint (Q z) (W z))
    (hQ : ∀ z ∈ C, Q z ⊆ S ∪ C) (hW : ∀ z ∈ C, W z ⊆ S)
    (hsize : ∀ z ∈ C, (Q z).card+(W z).card=d+1)
    (hxQ : ∀ z ∈ C, x ∉ Q z) (hyQ : ∀ z ∈ C, y ∉ Q z)
    (hzQ : ∀ z ∈ C, ∀ q ∈ Q z, H.Adj z q)
    (hcross : ∀ z ∈ C, ∀ q ∈ Q z, ∀ w ∈ W z, H.Adj q w)
    (hWmin : ∀ z ∈ C, 4 ≤ (W z).card)
    (hprod : ∀ z ∈ C, L ≤ (W z).card * (Q z).card) :
    L * C.card + 1 ≤ (d-1)*(d-2)*(d-3) := by
  classical
  let Z : V → Finset V := fun q => if q ∈ C then insert q ((H.neighborFinset q) ∩ C) else ((H.neighborFinset q) ∩ C)
  let D : V → Finset V := fun w => (((H.neighborFinset w).erase x).erase y).filter
    (fun q => q ∈ S ∨ (q ∈ C ∧ 4 ≤ ((H.neighborFinset q) ∩ S).card))
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
        by_cases hqC : q ∈ C
        · have hqS : q ∉ S := fun h => (Finset.disjoint_left.mp hSC) h hqC
          have hfour : 4 ≤ ((H.neighborFinset q) ∩ S).card := by
            rcases hq'.2 with h | ⟨_,h⟩
            · exact (hqS h).elim
            · exact h
          have hc := external_neighbor_count_with_four_internal H q S C d hSC (hmax q) hfour
          have hnot : q ∉ ((H.neighborFinset q) ∩ C) := by simp
          dsimp [Z]
          rw [if_pos hqC, Finset.card_insert_of_notMem hnot]
          omega
        · have hqtype : q ∈ S ∨ (q ∈ C ∧ 3 ≤ ((H.neighborFinset q) ∩ S).card) := by
            rcases hq'.2 with h | ⟨hc,h4⟩
            · exact Or.inl h
            · exact Or.inr ⟨hc,by omega⟩
          have hc := external_neighbor_count_at_most_degree_sub_three H x y w q hxy S C d hSC hxC hyC hw hSxy hqw (hmax q) hqtype
          simpa [Z,hqC] using hc
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
    have hqgood : p.2 ∈ S ∨ (p.2 ∈ C ∧ 4 ≤ ((H.neighborFinset p.2) ∩ S).card) := by
      rcases Finset.mem_union.mp (hQ z hz hq) with hs | hc
      · exact Or.inl hs
      · right
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
    by_cases hpC : p.2 ∈ C
    · simp only [Z,if_pos hpC,Finset.mem_insert]
      exact Or.inr (Finset.mem_inter.mpr ⟨hzN,hz⟩)
    · simp only [Z,if_neg hpC]
      exact Finset.mem_inter.mpr ⟨hzN,hz⟩
  obtain ⟨z0,hz0⟩ := hC
  have htwo := bridge_opposite_shore_has_two_external_vertices S C (Q z0) (W z0) d hSC
    (hdis z0 hz0) (hQ z0 hz0) (hW z0 hz0) hSsize (hsize z0 hz0)
  obtain ⟨q0,hq0⟩ := Finset.card_pos.mp (by omega : 0 < (Q z0 ∩ C).card)
  have hqQ : q0 ∈ Q z0 := (Finset.mem_inter.mp hq0).1
  have hqC : q0 ∈ C := (Finset.mem_inter.mp hq0).2
  obtain ⟨w0,hw0⟩ := Finset.card_pos.mp (by have := hWmin z0 hz0; omega : 0 < (W z0).card)
  have hwS : w0 ∈ S := hW z0 hz0 hw0
  have hqN : q0 ∈ H.neighborFinset w0 := by simpa using (hcross z0 hz0 q0 hqQ w0 hw0).symm
  have hqx : q0 ≠ x := fun he => hxQ z0 hz0 (he ▸ hqQ)
  have hqy : q0 ≠ y := fun he => hyQ z0 hz0 (he ▸ hqQ)
  have hqS4 : 4 ≤ ((H.neighborFinset q0) ∩ S).card := by
    have hWsub : W z0 ⊆ (H.neighborFinset q0) ∩ S := by
      intro w hw
      exact Finset.mem_inter.mpr ⟨by simpa using hcross z0 hz0 q0 hqQ w hw,hW z0 hz0 hw⟩
    have hc := Finset.card_le_card hWsub
    have hm := hWmin z0 hz0
    omega
  have hqD : q0 ∈ D w0 := Finset.mem_filter.mpr
    ⟨Finset.mem_erase.mpr ⟨hqy,Finset.mem_erase.mpr ⟨hqx,hqN⟩⟩, Or.inr ⟨hqC,hqS4⟩⟩
  have hmissingUpper : ((w0,q0),q0) ∈ upper := by
    apply Finset.mem_biUnion.mpr
    refine ⟨w0,hwS,Finset.mem_biUnion.mpr ⟨q0,hqD,?_⟩⟩
    apply Finset.mem_image.mpr
    refine ⟨q0, ?_, rfl⟩
    simp [Z,hqC]
  have hmissingLower : ((w0,q0),q0) ∉ lower := by
    intro h
    obtain ⟨z,hz,ht⟩ := Finset.mem_biUnion.mp h
    obtain ⟨p,hp,he⟩ := Finset.mem_image.mp ht
    have hpq : p.2 = q0 := congrArg (fun t : (V × V) × V => t.1.2) he
    have hzq : z = q0 := congrArg Prod.snd he
    have hpQ : p.2 ∈ Q z := (Finset.mem_product.mp hp).2
    have hh := hzQ z hz p.2 hpQ
    rw [hpq,hzq] at hh
    exact H.irrefl hh
  have hstrict : lower ⊂ upper := Finset.ssubset_iff_subset_ne.mpr
    ⟨hsub, fun he => hmissingLower (he.symm ▸ hmissingUpper)⟩
  have hlt := Finset.card_lt_card hstrict
  have hbound := lt_of_le_of_lt hlower (lt_of_lt_of_le hlt hupper)
  have hS : S.card = d-1 := by omega
  rw [hS] at hbound
  have := Nat.succ_le_of_lt hbound
  simpa [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using this
