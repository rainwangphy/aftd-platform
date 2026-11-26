import AFTD.Prelude
import AFTD.Kb.Tcs.Op1957OddComponentsAmbientPartition

/-!
# k7_at_most_four_odd_components

Topic: graphs   Node: 9de3427b65ae

Provenance: helper lemma. Balanced-cut k=7 reduction for OP-1957; https://arxiv.org/abs/2611.22690.

In the stated order-28 high-degree graph, a 14-vertex induced side has at most four odd components.
-/

theorem k7_at_most_four_odd_components
    (G : SimpleGraph (Fin 28)) [DecidableRel G.Adj]
    (hdegree : ∀ v, 15 ≤ (G.neighborFinset v).card)
    (C : Finset (Fin 28)) (hcard : C.card=14) :
    (G.induce {v | v ∉ C}).oddComponents.ncard ≤ 4 := by
  set_option maxHeartbeats 4000000 in
    classical
    let U : Finset (Fin 28) := Cᶜ
    have hUcard : U.card=14 := by
      have hh := Finset.card_compl C
      simp only [Fintype.card_fin] at hh
      dsimp [U]
      omega
    have hs : {v : Fin 28 | v ∈ U} = {v : Fin 28 | v ∉ C} := by ext v; simp [U]
    let H := G.induce {v | v ∈ U}
    have hHcard : Nat.card {v : Fin 28 | v ∈ U} = 14 := by
      rw [Nat.card_coe_set_eq]
      change (U : Set (Fin 28)).ncard = 14
      rw [Set.ncard_coe_finset,hUcard]
    have hpar := SimpleGraph.odd_ncard_oddComponents H
    rw [hHcard,Nat.odd_iff,Nat.odd_iff] at hpar
    by_contra hnot
    have hq : 6 ≤ H.oddComponents.ncard := by
      have hn' : ¬ H.oddComponents.ncard ≤ 4 := by
        change ¬ (G.induce {v | v ∈ U}).oddComponents.ncard ≤ 4
        rw [hs]
        exact hnot
      omega
    obtain ⟨F,hF,hdis,hcover⟩ := op1957_odd_components_ambient_partition G U 6 (by omega) hq (by omega)
    have hmin : ∀ i : Fin 6, 3 ≤ (F i).card := by
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
    have hpairdis : (↑(Finset.univ : Finset (Fin 6)) : Set (Fin 6)).PairwiseDisjoint F := by
      intro i hi j hj hij
      exact (hdis i j hij).1
    have hsum : ∑ i : Fin 6, (F i).card = 14 := by
      rw [← Finset.card_biUnion hpairdis,hcover,hUcard]
    have hlower : (∑ i : Fin 6, 3) ≤ ∑ i : Fin 6, (F i).card := by
      apply Finset.sum_le_sum
      intro i hi
      exact hmin i
    simp at hlower
    omega
