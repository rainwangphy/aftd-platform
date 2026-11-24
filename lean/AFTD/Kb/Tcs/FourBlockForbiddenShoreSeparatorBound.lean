import AFTD.Prelude

/-!
# four_block_forbidden_shore_separator_bound

Topic: graphs   Node: 63f2db48a636

Provenance: helper lemma. OP-1957: a forbidden-block shore cut found from the zero-defect relaxations.

In a 2L-vertex graph with the stated L-vertex separator property, disjoint blocks A, B, D, anticomplete A and B of total size L, and a nonempty Q∩A anticomplete to W∩D, the sizes of Q∩A and W∩D sum to at most |A|.
-/

theorem four_block_forbidden_shore_separator_bound
    (L : ℕ) (G : SimpleGraph (Fin (2*L))) [DecidableRel G.Adj]
    (A B D Q W : Finset (Fin (2*L)))
    (hAB : Disjoint A B) (hAD : Disjoint A D) (hBD : Disjoint B D)
    (hsize : A.card+B.card=L) (hB : B.Nonempty)
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hcross : ∀ a ∈ Q ∩ A, ∀ d ∈ W ∩ D, ¬ G.Adj a d)
    (hsep : ∀ X U V : Finset (Fin (2*L)), U.Nonempty → V.Nonempty →
      Disjoint X U → Disjoint X V → Disjoint U V → X ∪ U ∪ V = Finset.univ →
      (∀ u ∈ U, ∀ v ∈ V, ¬ G.Adj u v) → L ≤ X.card)
    (hne : (Q ∩ A).Nonempty) :
    (Q ∩ A).card + (W ∩ D).card ≤ A.card := by
  classical
  let U := B ∪ (W ∩ D)
  let V := Q ∩ A
  let X := Finset.univ \ (U ∪ V)
  have hUne : U.Nonempty := by
    obtain ⟨b,hb⟩ := hB
    exact ⟨b, Finset.mem_union_left _ hb⟩
  have hVne : V.Nonempty := hne
  have hUV : Disjoint U V := by
    apply Finset.disjoint_left.mpr
    intro z hzU hzV
    simp only [U,V,Finset.mem_union,Finset.mem_inter] at hzU hzV
    rcases hzU with hzB | ⟨hzW,hzD⟩
    · exact Finset.disjoint_left.mp hAB hzV.2 hzB
    · exact Finset.disjoint_left.mp hAD hzV.2 hzD
  have hXU : Disjoint X U := by
    apply Finset.disjoint_left.mpr
    intro z hzX hzU
    exact (Finset.mem_sdiff.mp hzX).2 (Finset.mem_union_left _ hzU)
  have hXV : Disjoint X V := by
    apply Finset.disjoint_left.mpr
    intro z hzX hzV
    exact (Finset.mem_sdiff.mp hzX).2 (Finset.mem_union_right _ hzV)
  have hcover : X ∪ U ∪ V = Finset.univ := by
    ext z
    simp [X]
  have hanti : ∀ u ∈ U, ∀ v ∈ V, ¬ G.Adj u v := by
    intro u hu v hv huv
    simp only [U,V,Finset.mem_union,Finset.mem_inter] at hu hv
    rcases hu with huB | ⟨huW,huD⟩
    · exact hnoAB v hv.2 u huB huv.symm
    · exact hcross v (Finset.mem_inter.mpr hv) u (Finset.mem_inter.mpr ⟨huW,huD⟩) huv.symm
  have hcut := hsep X U V hUne hVne hXU hXV hUV hcover hanti
  have hdis : Disjoint B (W ∩ D) :=
    Finset.disjoint_of_subset_right Finset.inter_subset_right hBD
  have hUcard : U.card = B.card + (W ∩ D).card := Finset.card_union_of_disjoint hdis
  have hUVcard : (U ∪ V).card = U.card + V.card := Finset.card_union_of_disjoint hUV
  have htotal := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (Fin (2*L))) (U ∪ V)
  simp only [Finset.univ_inter, Finset.card_univ, Fintype.card_fin] at htotal
  change X.card + (U ∪ V).card = 2*L at htotal
  rw [hUVcard,hUcard] at htotal
  change X.card + (B.card + (W ∩ D).card + (Q ∩ A).card) = 2*L at htotal
  omega
