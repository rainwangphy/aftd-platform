import AFTD.Prelude
import AFTD.Kb.Tcs.Op1957OddComponentsAmbientPartition
import AFTD.Kb.Tcs.BoundaryFiveOddSaturatedEmptyBarrierForcePatterns

/-!
# op1957_ambient_odd_shores_to_component_barrier

Topic: graphs   Node: 80072b5d93b5

Provenance: helper lemma. OP-1957: transfer from ambient odd shores to a component barrier

An ambient odd-shore obstruction can be represented as disjoint odd endpoint shores, odd anticomplete groups, and a disjoint barrier of the same cardinality as the group family, with the total size preserved.
-/

set_option maxHeartbeats 2000000

theorem op1957_ambient_odd_shores_to_component_barrier
    (k : ℕ) (G : SimpleGraph (Fin (4*k)))
    (X Y U : Finset (Fin (4*k))) (s : ℕ) (x y : Fin (4*k))
    (hXY : Disjoint X Y) (hXU : Disjoint X U) (hYU : Disjoint Y U)
    (hx : x ∈ X) (hy : y ∈ Y) (hoddX : Odd X.card) (hoddY : Odd Y.card)
    (hsize : X.card+Y.card+U.card+s=2*k)
    (hUodd : s ≤ (G.induce {v | v ∈ U}).oddComponents.ncard)
    (hUpar : U.card % 2 = s % 2)
    (hcross : ∀ a ∈ X, ∀ b ∈ Y, G.Adj a b → a=x ∧ b=y)
    (hantiX : ∀ a ∈ X, ∀ u ∈ U, ¬ G.Adj a u)
    (hantiY : ∀ b ∈ Y, ∀ u ∈ U, ¬ G.Adj b u) :
    ∃ (Y' S : Finset (Fin (4*k))) (t : ℕ) (T : Fin t → Finset (Fin (4*k))),
      x ∈ X ∧ y ∈ Y' ∧ Disjoint X Y' ∧ Disjoint X S ∧ Disjoint Y' S ∧
      (∀ i, Disjoint X (T i)) ∧ (∀ i, Disjoint Y' (T i)) ∧
      (∀ i, Disjoint S (T i)) ∧ (∀ i j, i ≠ j → Disjoint (T i) (T j)) ∧
      Odd X.card ∧ Odd Y'.card ∧ (∀ i, Odd (T i).card) ∧ S.card=t ∧
      (X ∪ Y' ∪ Finset.univ.biUnion T ∪ S).card=2*k ∧
      (∀ a ∈ X, ∀ b ∈ Y', G.Adj a b → a=x ∧ b=y) ∧
      (∀ i, ∀ a ∈ X, ∀ u ∈ T i, ¬ G.Adj a u) ∧
      (∀ i, ∀ b ∈ Y', ∀ u ∈ T i, ¬ G.Adj b u) ∧
      (∀ i j, i ≠ j → ∀ u ∈ T i, ∀ v ∈ T j, ¬ G.Adj u v) := by
  classical
  by_cases hs : s=0
  · have hsize0 : X.card+Y.card+U.card=2*k := by omega
    have hanti : ∀ u ∈ U, ∀ a ∈ X, ¬ G.Adj u a := by
      intro u hu a ha h
      exact hantiX a ha u hu h.symm
    obtain ⟨hXYU,hXYUsize,_,hyYU,hoddYU,hcrossYU⟩ :=
      in1159_absorb_even_reservoir_of_even_total G X Y U x y k hXY hXU hYU hsize0 hx hy hcross hanti hoddX hoddY
    refine ⟨Y ∪ U,∅,0,fun i => Fin.elim0 i, hx,hyYU,hXYU,by simp,by simp,?_,?_,?_,?_,hoddX,hoddYU,?_,by simp,?_,hcrossYU,?_,?_,?_⟩
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
    · simpa [Finset.card_union_of_disjoint hXYU] using hXYUsize
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
  · have hspos : 1 ≤ s := by omega
    obtain ⟨T,hTodd,hTdis,hTcover⟩ := op1957_odd_components_ambient_partition G U s hspos hUodd hUpar
    let W := X ∪ Y ∪ U
    have hXYU : Disjoint (X ∪ Y) U := Finset.disjoint_union_left.mpr ⟨hXU,hYU⟩
    have hWcard : W.card=X.card+Y.card+U.card := by
      simp only [W,Finset.card_union_of_disjoint hXYU,Finset.card_union_of_disjoint hXY]
    have hscard : s ≤ ((Finset.univ : Finset (Fin (4*k))) \ W).card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ W)]
      simp only [Finset.card_univ,Fintype.card_fin]
      omega
    obtain ⟨S,hSsub,hSsize⟩ := Finset.exists_subset_card_eq hscard
    have hWS : Disjoint W S := by
      apply Finset.disjoint_left.mpr
      intro v hvw hvs
      exact (Finset.mem_sdiff.mp (hSsub hvs)).2 hvw
    have hXS : Disjoint X S := Finset.disjoint_of_subset_left
      (Finset.Subset.trans (Finset.subset_union_left : X ⊆ X ∪ Y) Finset.subset_union_left) hWS
    have hYS : Disjoint Y S := Finset.disjoint_of_subset_left
      (Finset.Subset.trans (Finset.subset_union_right : Y ⊆ X ∪ Y) Finset.subset_union_left) hWS
    have hUS : Disjoint U S := Finset.disjoint_of_subset_left Finset.subset_union_right hWS
    have hXT : ∀ i, Disjoint X (T i) := by
      intro i; exact Finset.disjoint_of_subset_right (hTodd i).1 hXU
    have hYT : ∀ i, Disjoint Y (T i) := by
      intro i; exact Finset.disjoint_of_subset_right (hTodd i).1 hYU
    have hST : ∀ i, Disjoint S (T i) := by
      intro i; exact Finset.disjoint_of_subset_right (hTodd i).1 hUS.symm
    refine ⟨Y,S,s,T,hx,hy,hXY,hXS,hYS,hXT,hYT,hST,?_,hoddX,hoddY,?_,hSsize,?_,hcross,?_,?_,?_⟩
    · intro i j hij; exact (hTdis i j hij).1
    · intro i; exact (hTodd i).2
    · rw [hTcover]
      change (W ∪ S).card=2*k
      rw [Finset.card_union_of_disjoint hWS,hWcard,hSsize]
      omega
    · intro i a ha u hu; exact hantiX a ha u ((hTodd i).1 hu)
    · intro i b hb u hu; exact hantiY b hb u ((hTodd i).1 hu)
    · intro i j hij; exact (hTdis i j hij).2
