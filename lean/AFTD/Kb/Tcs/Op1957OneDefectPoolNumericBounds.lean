import AFTD.Prelude
import AFTD.Kb.Tcs.Op1957BarrierRepresentativeCountBound
import AFTD.Kb.Tcs.FinsetCardEqSumFourBlockInter
import AFTD.Kb.Tcs.AnticompleteVertexFourDisjointNonneighborSetsBound

/-!
# op1957_one_defect_pool_numeric_bounds

Topic: graphs   Node: 19055e9c7efb

Provenance: helper lemma. OP-1957: five-by-odd boundary reduction, arXiv:2611.22690

Under the displayed four-block degree and anticomplete-group hypotheses, each of the three listed inequalities follows when the pool meets A, C or D respectively.
-/

theorem op1957_one_defect_pool_numeric_bounds
    {I : Type*} [DecidableEq I] (k c : ℕ) (hc : 5 ≤ c) (hkc : c ≤ k)
    (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (A B C D X Y : Finset (Fin (4*k)))
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (hcover : A ∪ B ∪ C ∪ D = Finset.univ)
    (hA : A.card=5) (hB : B.card=2*k-5) (hC : C.card=c) (hD : D.card=2*k-c)
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hnoCD : ∀ a ∈ C, ∀ b ∈ D, ¬ G.Adj a b)
    (hdegree : ∀ v, 2*k+2 ≤ (G.neighborFinset v).card)
    (K : Finset I) (T : I → Finset (Fin (4*k)))
    (hodd : ∀ i ∈ K, Odd (T i).card)
    (hTT : ∀ i ∈ K, ∀ j ∈ K, i ≠ j → Disjoint (T i) (T j))
    (hXY : Disjoint X Y) (hXT : ∀ i ∈ K, Disjoint X (T i)) (hYT : ∀ i ∈ K, Disjoint Y (T i))
    (hantiXT : ∀ i ∈ K, ∀ u ∈ X, ∀ v ∈ T i, ¬ G.Adj u v)
    (hantiYT : ∀ i ∈ K, ∀ u ∈ Y, ∀ v ∈ T i, ¬ G.Adj u v)
    (hantiTT : ∀ i ∈ K, ∀ j ∈ K, i ≠ j → ∀ u ∈ T i, ∀ v ∈ T j, ¬ G.Adj u v) :
    let U := K.biUnion T
    ((U ∩ A).Nonempty → (X ∩ A).card+(X ∩ C).card+(X ∩ D).card+
      (Y ∩ A).card+(Y ∩ C).card+(Y ∩ D).card ≤ 2) ∧
    ((U ∩ C).Nonempty → (X ∩ A).card+(X ∩ B).card+(X ∩ C).card+
      (Y ∩ A).card+(Y ∩ B).card+(Y ∩ C).card+K.card+2 ≤ c+(U ∩ D).card) ∧
    ((U ∩ D).Nonempty → (X ∩ A).card+(X ∩ B).card+(X ∩ D).card+
      (Y ∩ A).card+(Y ∩ B).card+(Y ∩ D).card+K.card+c+2 ≤ 2*k+(U ∩ C).card) := by
  classical
  let U := K.biUnion T
  have hne : ∀ i ∈ K, (T i).Nonempty := by
    intro i hi
    apply Finset.card_pos.mp
    obtain ⟨n,hn⟩ := hodd i hi
    omega
  have hparts (P : Finset (Fin (4*k))) := finset_card_eq_sum_four_block_inter A B C D P hAB hAC hAD hBC hBD hCD hcover
  have hdiffB (P : Finset (Fin (4*k))) : (P \ B).card = (P ∩ A).card+(P ∩ C).card+(P ∩ D).card := by
    have hs := hparts P; have hd := Finset.card_inter_add_card_sdiff P B; omega
  have hdiffC (P : Finset (Fin (4*k))) : (P \ C).card = (P ∩ A).card+(P ∩ B).card+(P ∩ D).card := by
    have hs := hparts P; have hd := Finset.card_inter_add_card_sdiff P C; omega
  have hdiffD (P : Finset (Fin (4*k))) : (P \ D).card = (P ∩ A).card+(P ∩ B).card+(P ∩ C).card := by
    have hs := hparts P; have hd := Finset.card_inter_add_card_sdiff P D; omega
  have hfind (Q : Finset (Fin (4*k))) (h : (U ∩ Q).Nonempty) : ∃ j ∈ K, ∃ q ∈ T j, q ∈ Q := by
    obtain ⟨q,hq⟩ := h
    obtain ⟨j,hj,hqj⟩ := Finset.mem_biUnion.mp (Finset.mem_inter.mp hq).1
    exact ⟨j,hj,q,hqj,(Finset.mem_inter.mp hq).2⟩
  have hrep (Q : Finset (Fin (4*k))) (j : I) (hj : j ∈ K) (q : Fin (4*k)) (hq : q ∈ T j)
      (hqQ : q ∉ Q) (hQ : ∀ z ∈ Q, ¬ G.Adj q z)
      (d r : ℕ) (hsize : Fintype.card (Fin (4*k)) = Q.card+d+1)
      (hdeg : d ≤ (G.neighborFinset q).card+r) :=
    op1957_barrier_representative_count_bound G Q X Y K T j hj hne hTT hXY hXT hYT q hq hqQ hQ
      (fun z hz h => hantiXT j hj z hz q hq h.symm)
      (fun z hz h => hantiYT j hj z hz q hq h.symm)
      (fun i hi hij z hz => hantiTT j hj i hi hij.symm q hq z hz)
      d r hsize hdeg
  refine ⟨?_,?_,?_⟩
  · intro hUA
    obtain ⟨j,hj,q,hq,hqA⟩ := hfind A hUA
    have hqB : q ∉ B := fun h => Finset.disjoint_left.mp hAB hqA h
    have hqX : q ∉ X := fun h => Finset.disjoint_left.mp (hXT j hj) h hq
    have hqY : q ∉ Y := fun h => Finset.disjoint_left.mp (hYT j hj) h hq
    have hs : ∀ z, (z ∈ X ∨ z ∈ Y ∨ z ∈ (∅ : Finset (Fin (4*k))) ∨ z ∈ (∅ : Finset (Fin (4*k)))) → z ≠ q ∧ ¬ G.Adj q z := by
      intro z hz
      rcases hz with hz | hz | hz | hz
      · exact ⟨fun he => hqX (he ▸ hz),fun h => hantiXT j hj z hz q hq h.symm⟩
      · exact ⟨fun he => hqY (he ▸ hz),fun h => hantiYT j hj z hz q hq h.symm⟩
      · simp at hz
      · simp at hz
    have hh := anticomplete_vertex_four_disjoint_nonneighbor_sets_bound G B q hqB (hnoAB q hqA) (2*k+4) 2
      (by simp only [Fintype.card_fin]; omega) (by have := hdegree q; omega)
      X Y ∅ ∅ hs hXY (by simp) (by simp) (by simp) (by simp) (by simp)
    simp only [Finset.empty_sdiff,Finset.card_empty,add_zero,hdiffB] at hh
    omega
  · intro hUC
    obtain ⟨j,hj,q,hq,hqC⟩ := hfind C hUC
    have hqD : q ∉ D := fun h => Finset.disjoint_left.mp hCD hqC h
    have hh := hrep D j hj q hq hqD (hnoCD q hqC) (2*k+c-1) (c-3)
      (by simp only [Fintype.card_fin]; omega) (by have := hdegree q; omega)
    rw [hdiffD X,hdiffD Y] at hh
    omega
  · intro hUD
    obtain ⟨j,hj,q,hq,hqD⟩ := hfind D hUD
    have hqC : q ∉ C := fun h => Finset.disjoint_left.mp hCD h hqD
    have hQ : ∀ z ∈ C, ¬ G.Adj q z := fun z hz h => hnoCD z hz q hqD h.symm
    have hh := hrep C j hj q hq hqC hQ (4*k-c-1) (2*k-c-3)
      (by simp only [Fintype.card_fin]; omega) (by have := hdegree q; omega)
    rw [hdiffC X,hdiffC Y] at hh
    omega
