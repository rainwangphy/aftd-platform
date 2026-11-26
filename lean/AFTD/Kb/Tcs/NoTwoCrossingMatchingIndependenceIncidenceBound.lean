import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.ExtendibleMatchableTwoKVerticesComplementMatchable
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# no_two_crossing_matching_independence_incidence_bound

Topic: graphs   Node: 29ce1236d5a9

Provenance: helper lemma. Balanced-cut reduction for OP-1957; https://arxiv.org/abs/1011.3384.

If distinct vertices of U cannot cross to adjacent vertices of R, |U|=2r, |R|=2k, a (k−r)-matching inside R and α≤k imply e(U,R)≤2rk+2r.
-/

theorem no_two_crossing_matching_independence_incidence_bound
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (U R : Finset V) (r k : ℕ) (hr : 1 ≤ r)
    (hU : U.card = 2*r) (hR : R.card = 2*k)
    (N : G.Subgraph) (hN : N.IsMatching) (hNR : N.verts ⊆ (R : Set V))
    (hNcard : N.edgeSet.ncard + r = k)
    (hforbid : ∀ u ∈ U, ∀ v ∈ U, u ≠ v → ∀ x ∈ R, ∀ y ∈ R,
      G.Adj u x → G.Adj v y → ¬ G.Adj x y)
    (hind : ∀ I : Finset V, (∀ x ∈ I, ∀ y ∈ I, x ≠ y → ¬ G.Adj x y) → I.card ≤ k) :
    (∑ u ∈ U, ((G.neighborFinset u) ∩ R).card) ≤ 2*r*k + 2*r := by
  set_option maxHeartbeats 4000000 in
    classical
    let K : V → Finset V := fun x => U.filter (fun u => G.Adj u x)
    let B : Finset V := R.filter (fun x => 2 ≤ (K x).card)
    let Z : Finset V := R.filter (fun x => (K x).card = 0)
    have hKR : ∀ x, (K x).card ≤ 2*r := by
      intro x
      have hh := Finset.card_filter_le U (fun u => G.Adj u x)
      simpa [K,hU] using hh
    have hBsub : B ⊆ R := Finset.filter_subset _ _
    have hZsub : Z ⊆ R := Finset.filter_subset _ _
    have hBZ : Disjoint B Z := by
      apply Finset.disjoint_left.mpr
      intro x hxB hxZ
      have hb := (Finset.mem_filter.mp hxB).2
      have hz := (Finset.mem_filter.mp hxZ).2
      omega
    have hno : ∀ x ∈ B, ∀ y ∈ R, G.Adj x y → y ∈ Z := by
      intro x hxB y hyR hxy
      have hxR := hBsub hxB
      have hxcard : 2 ≤ (K x).card := (Finset.mem_filter.mp hxB).2
      apply Finset.mem_filter.mpr
      refine ⟨hyR,?_⟩
      by_contra hn
      have hpos : 0 < (K y).card := Nat.pos_of_ne_zero hn
      obtain ⟨v,hv⟩ := Finset.card_pos.mp hpos
      have hvU : v ∈ U := (Finset.mem_filter.mp hv).1
      have hvy : G.Adj v y := (Finset.mem_filter.mp hv).2
      have hnsub : ¬ K x ⊆ {v} := by
        intro hh
        have hc := Finset.card_le_card hh
        simp at hc
        omega
      obtain ⟨u,hu,huv⟩ := Finset.not_subset.mp hnsub
      have huU : u ∈ U := (Finset.mem_filter.mp hu).1
      have hux : G.Adj u x := (Finset.mem_filter.mp hu).2
      have huv' : u ≠ v := by simpa using huv
      exact hforbid u huU v hvU huv' x hxR y hyR hux hvy hxy
    have hBind : ∀ x ∈ B, ∀ y ∈ B, x ≠ y → ¬ G.Adj x y := by
      intro x hx y hy hne hxy
      have hyZ := hno x hx y (hBsub hy) hxy
      exact Finset.disjoint_left.mp hBZ hy hyZ
    have hBcard : B.card ≤ k := hind B hBind
    let D : Finset V := N.verts.toFinset
    have hDcard : D.card = 2*N.edgeSet.ncard := by
      dsimp [D]
      rw [← Set.ncard_eq_toFinset_card']
      exact (in1076_matching_twice_card hN).symm
    have hDR : D ⊆ R := by
      intro x hx
      exact hNR (by simpa [D] using hx)
    let Q : Finset V := B ∩ D
    have hQZ : Q.card ≤ Z.card := by
      let f : {x // x ∈ Q} → {y // y ∈ Z} := fun x =>
        let hxD : x.val ∈ N.verts := by
          have hx := (Finset.mem_inter.mp x.property).2
          simpa [D] using hx
        let y := Classical.choose (hN hxD)
        ⟨y, hno x.val (Finset.mem_inter.mp x.property).1 y
          (hNR (N.edge_vert (Classical.choose_spec (hN hxD)).1.symm))
          (N.adj_sub (Classical.choose_spec (hN hxD)).1)⟩
      have hinj : Function.Injective f := by
        intro a b hab
        let haD : a.val ∈ N.verts := by
          have ha := (Finset.mem_inter.mp a.property).2
          simpa [D] using ha
        let hbD : b.val ∈ N.verts := by
          have hb := (Finset.mem_inter.mp b.property).2
          simpa [D] using hb
        let ya := Classical.choose (hN haD)
        let yb := Classical.choose (hN hbD)
        have he : ya=yb := by
          have hh := congrArg Subtype.val hab
          change ya = yb at hh
          exact hh
        have hay : N.Adj ya a.val := (Classical.choose_spec (hN haD)).1.symm
        have hby : N.Adj ya b.val := by
          rw [he]
          exact (Classical.choose_spec (hN hbD)).1.symm
        have hya : ya ∈ N.verts := N.edge_vert hay
        apply Subtype.ext
        exact (hN hya).unique hay hby
      have hh := Fintype.card_le_of_injective f hinj
      simpa using hh
    have hBbound : B.card ≤ Z.card+2*r := by
      have hbd : (B \ D) ⊆ R \ D := by
        intro x hx
        exact Finset.mem_sdiff.mpr ⟨hBsub (Finset.mem_sdiff.mp hx).1,(Finset.mem_sdiff.mp hx).2⟩
      have hb := Finset.card_le_card hbd
      have hRD := Finset.card_sdiff_add_card_eq_card hDR
      have hBD := Finset.card_sdiff_add_card_inter B D
      dsimp [Q] at hQZ
      omega
    have hsumEq : (∑ u ∈ U, ((G.neighborFinset u) ∩ R).card) = ∑ x ∈ R, (K x).card := by
      have hAbove : ∀ u, R.filter (fun x => G.Adj u x) = (G.neighborFinset u) ∩ R := by
        intro u
        ext x
        simp [and_comm]
      have hh := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s:=U) (t:=R) G.Adj
      simp only [Finset.bipartiteAbove,Finset.bipartiteBelow,hAbove] at hh
      simpa [K] using hh
    let L : Finset V := R \ (B ∪ Z)
    have hL : ∀ x ∈ L, (K x).card ≤ 1 := by
      intro x hx
      have hnB : x ∉ B := by
        intro h
        exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_union_left Z h)
      have hxR : x ∈ R := (Finset.mem_sdiff.mp hx).1
      by_contra hn
      apply hnB
      exact Finset.mem_filter.mpr ⟨hxR,by omega⟩
    have hcover : B ∪ Z ∪ L = R := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_union.mp hx with hx | hx
        · rcases Finset.mem_union.mp hx with hx | hx
          · exact hBsub hx
          · exact hZsub hx
        · exact (Finset.mem_sdiff.mp hx).1
      · intro hx
        by_cases hb : x ∈ B
        · exact Finset.mem_union_left L (Finset.mem_union_left Z hb)
        · by_cases hz : x ∈ Z
          · exact Finset.mem_union_left L (Finset.mem_union_right B hz)
          · apply Finset.mem_union_right
            exact Finset.mem_sdiff.mpr ⟨hx,by simp [hb,hz]⟩
    have hdisBL : Disjoint B L := by
      apply Finset.disjoint_left.mpr
      intro x hxB hxL
      exact (Finset.mem_sdiff.mp hxL).2 (Finset.mem_union_left Z hxB)
    have hdisZL : Disjoint Z L := by
      apply Finset.disjoint_left.mpr
      intro x hxZ hxL
      exact (Finset.mem_sdiff.mp hxL).2 (Finset.mem_union_right B hxZ)
    have hBL : Disjoint (B ∪ Z) L := Finset.disjoint_union_left.mpr ⟨hdisBL,hdisZL⟩
    have hsumBound : (∑ x ∈ R, (K x).card) ≤ 2*r*B.card+L.card := by
      rw [← hcover,Finset.sum_union hBL,Finset.sum_union hBZ]
      have hsumB : (∑ x ∈ B, (K x).card) ≤ 2*r*B.card := by
        have hh := Finset.sum_le_sum (s:=B) (fun x _ => hKR x)
        simpa [Nat.mul_comm] using hh
      have hsumZ : (∑ x ∈ Z, (K x).card) = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        exact (Finset.mem_filter.mp hx).2
      have hsumL : (∑ x ∈ L, (K x).card) ≤ L.card := by
        have hh := Finset.sum_le_sum (s:=L) hL
        simpa using hh
      omega
    have hcardR : B.card + Z.card + L.card = 2*k := by
      have hh := Finset.card_union_of_disjoint hBL
      have hg := Finset.card_union_of_disjoint hBZ
      rw [hcover,hR] at hh
      omega
    have hr2 : 2 ≤ 2*r := by omega
    have hrw : 2*r-2+2 = 2*r := by omega
    have hprod := Nat.mul_le_mul_left (2*r-2) hBcard
    have hpB := congrArg (fun n : ℕ => n*B.card) hrw
    have hpK := congrArg (fun n : ℕ => n*k) hrw
    simp only [Nat.add_mul] at hpB hpK
    rw [hsumEq]
    nlinarith
