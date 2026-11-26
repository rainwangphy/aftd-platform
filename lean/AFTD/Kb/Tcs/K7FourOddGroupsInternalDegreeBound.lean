import AFTD.Prelude
import AFTD.Kb.Tcs.Op1957OddComponentsAmbientPartition

/-!
# k7_four_odd_groups_internal_degree_bound

Topic: graphs   Node: 2214ea4aed16

Provenance: helper lemma. Balanced-cut k=7 reduction for OP-1957; https://arxiv.org/abs/2611.22690.

In an order-28 graph with the stated degree bound, four odd components on a 14-vertex side force each vertex there to have at most four neighbors on that side.
-/

theorem k7_four_odd_groups_internal_degree_bound
    (G : SimpleGraph (Fin 28)) [DecidableRel G.Adj]
    (hdegree : ∀ v, 15 ≤ (G.neighborFinset v).card)
    (C : Finset (Fin 28)) (hcard : C.card=14)
    (hodd : 4 ≤ (G.induce {v | v ∉ C}).oddComponents.ncard) :
    ∀ x, x ∉ C → ((G.neighborFinset x).filter (fun v => v ∉ C)).card ≤ 4 := by
  set_option maxHeartbeats 4000000 in
    classical
    let U : Finset (Fin 28) := Cᶜ
    have hUcard : U.card=14 := by
      have hh := Finset.card_compl C
      simp only [Fintype.card_fin] at hh
      dsimp [U]
      omega
    have hodd' : 4 ≤ (G.induce {v | v ∈ U}).oddComponents.ncard := by
      have hs : {v : Fin 28 | v ∈ U} = {v : Fin 28 | v ∉ C} := by ext v; simp [U]
      rw [hs]
      exact hodd
    obtain ⟨F,hF,hdis,hcover⟩ := op1957_odd_components_ambient_partition G U 4 (by omega) hodd' (by omega)
    have hmin : ∀ i : Fin 4, 3 ≤ (F i).card := by
      intro i
      have hi := (hF i).2
      have hpos : 0 < (F i).card := hi.pos
      obtain ⟨u,hu⟩ := Finset.card_pos.mp hpos
      have hnot : ¬ G.neighborFinset u ⊆ C := by
        intro h
        have hh := Finset.card_le_card h
        have hd := hdegree u
        omega
      obtain ⟨v,hvN,hvC⟩ := Finset.not_subset.mp hnot
      have huv : G.Adj u v := by simpa using hvN
      have hvU : v ∈ U := by simpa [U] using hvC
      have hvcover : v ∈ Finset.univ.biUnion F := by rw [hcover]; exact hvU
      obtain ⟨j,_,hvj⟩ := Finset.mem_biUnion.mp hvcover
      have hvF : v ∈ F i := by
        by_cases hij : i=j
        · simpa [hij] using hvj
        · exact False.elim ((hdis i j hij).2 u hu v hvj huv)
      have hne : u ≠ v := G.ne_of_adj huv
      have hpair : ({u,v} : Finset (Fin 28)) ⊆ F i := by
        intro x hx
        simp only [Finset.mem_insert,Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      have hh := Finset.card_le_card hpair
      rw [Finset.card_pair hne] at hh
      rw [Nat.odd_iff] at hi
      omega
    have hpairdis : (↑(Finset.univ : Finset (Fin 4)) : Set (Fin 4)).PairwiseDisjoint F := by
      intro i hi j hj hij
      exact (hdis i j hij).1
    have hsum : ∑ i : Fin 4, (F i).card = 14 := by
      rw [← Finset.card_biUnion hpairdis,hcover,hUcard]
    have hsum' : (F 0).card+(F 1).card+(F 2).card+(F 3).card=14 := by
      simpa [Fin.sum_univ_succ,add_assoc] using hsum
    have hmax : ∀ i : Fin 4, (F i).card ≤ 5 := by
      intro i
      have h0 := hmin 0
      have h1 := hmin 1
      have h2 := hmin 2
      have h3 := hmin 3
      have b0 : (F 0).card ≤ 5 := by omega
      have b1 : (F 1).card ≤ 5 := by omega
      have b2 : (F 2).card ≤ 5 := by omega
      have b3 : (F 3).card ≤ 5 := by omega
      fin_cases i <;> first | exact b0 | exact b1 | exact b2 | exact b3
    intro x hxC
    have hxU : x ∈ U := by simpa [U] using hxC
    have hxcover : x ∈ Finset.univ.biUnion F := by rw [hcover]; exact hxU
    obtain ⟨i,_,hxi⟩ := Finset.mem_biUnion.mp hxcover
    have hsub : (G.neighborFinset x).filter (fun v => v ∉ C) ⊆ (F i).erase x := by
      intro v hv
      have hvN := (Finset.mem_filter.mp hv).1
      have hvC := (Finset.mem_filter.mp hv).2
      have hxv : G.Adj x v := by simpa using hvN
      have hvU : v ∈ U := by simpa [U] using hvC
      have hvcover : v ∈ Finset.univ.biUnion F := by rw [hcover]; exact hvU
      obtain ⟨j,_,hvj⟩ := Finset.mem_biUnion.mp hvcover
      have hvi : v ∈ F i := by
        by_cases hij : i=j
        · simpa [hij] using hvj
        · exact False.elim ((hdis i j hij).2 x hxi v hvj hxv)
      exact Finset.mem_erase.mpr ⟨(G.ne_of_adj hxv).symm,hvi⟩
    have hh := Finset.card_le_card hsub
    have he := Finset.card_erase_add_one hxi
    have hmaxi := hmax i
    omega
