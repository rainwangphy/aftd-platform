import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraph
import AFTD.Kb.Tcs.DigraphCommonPredecessorOverlapIncidenceIdentity
import AFTD.Kb.Tcs.FiniteFamilyOverlapMultiplicityIdentity

/-!
# digraph_twenty_profile_overlap_cardinality_bound

Topic: graphs   Node: 41180695a8b8

Provenance: helper lemma. Internal common-predecessor pair counting for the twenty-cut equality profile; experiment 26344 tabulates consequences by part size.

If five vertices of a finite part have internal outdegrees 1 through 5 and all other part vertices have internal outdegree seven, the total common-predecessor overlap plus choose(|B|,2) plus 85 is at least 21|B|.
-/

theorem digraph_twenty_profile_overlap_cardinality_bound
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (B : Finset α) (low : Fin 5 → α) (hinj : Function.Injective low)
    (hmem : ∀ i, low i ∈ B)
    (hlow : ∀ i : Fin 5, (B.filter fun w => D.Adj (low i) w).card = i.val + 1)
    (hhigh : ∀ v ∈ B, (∀ i, v ≠ low i) → (B.filter fun w => D.Adj v w).card = 7) :
    21 * B.card ≤
      ((∑ v : α, Nat.choose (Finset.univ.filter fun w => D.Adj v w).card 2) -
        (digraph_common_predecessor_graph D).edgeFinset.card) + Nat.choose B.card 2 + 85 := by
  let outsB : α → Finset α := fun u => B.filter (fun w => D.Adj u w)
  let NB : α → Finset (Sym2 α) := fun u => (outsB u).offDiag.image Sym2.mk.uncurry
  let L : Finset α := Finset.univ.image low
  have hL_sub : L ⊆ B := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact hmem i
  have hL_card : L.card = 5 := by
    rw [Finset.card_image_of_injective Finset.univ hinj]
    simp
  have hsplit : ∑ v ∈ B, Nat.choose (outsB v).card 2 =
      (∑ v ∈ L, Nat.choose (outsB v).card 2) + ∑ v ∈ B \ L, Nat.choose (outsB v).card 2 := by
    rw [← Finset.sum_sdiff hL_sub, add_comm]
  have hsumL : ∑ v ∈ L, Nat.choose (outsB v).card 2 = 20 := by
    rw [Finset.sum_image (fun x _ y _ h => hinj h)]
    have heq : ∀ i : Fin 5, Nat.choose (outsB (low i)).card 2 = Nat.choose (i.val + 1) 2 := by
      intro i
      dsimp [outsB]
      rw [hlow i]
    simp_rw [heq]
    decide
  have hsumRest : ∑ v ∈ B \ L, Nat.choose (outsB v).card 2 = 21 * (B \ L).card := by
    have heq : ∀ v ∈ B \ L, Nat.choose (outsB v).card 2 = 21 := by
      intro v hv
      obtain ⟨hvB, hvNL⟩ := Finset.mem_sdiff.mp hv
      have hnot : ∀ i, v ≠ low i := by
        intro i heq
        apply hvNL
        apply Finset.mem_image.mpr
        exact ⟨i, Finset.mem_univ i, heq.symm⟩
      dsimp [outsB]
      rw [hhigh v hvB hnot]
      rfl
    rw [Finset.sum_congr rfl heq]
    simp [mul_comm]
  have hcards : (B \ L).card + 5 = B.card := by
    have := Finset.card_sdiff_add_card_eq_card hL_sub
    omega
  have hB_sum : 21 * B.card ≤ (∑ v ∈ B, Nat.choose (outsB v).card 2) + 85 := by
    rw [hsplit, hsumL, hsumRest]
    omega
  have hcard_NB : ∀ u, (NB u).card = Nat.choose (outsB u).card 2 := by
    intro u
    exact Sym2.card_image_offDiag (outsB u)
  have hsum_NB : (∑ a ∈ B, (NB a).card) = ∑ a ∈ B, Nat.choose (outsB a).card 2 := by
    apply Finset.sum_congr rfl
    intro u _
    exact hcard_NB u
  have hsub_all : B.biUnion NB ⊆ B.offDiag.image Sym2.mk.uncurry := by
    intro e he
    obtain ⟨u, -, heu⟩ := Finset.mem_biUnion.mp he
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp heu
    obtain ⟨hx, hy, hne⟩ := Finset.mem_offDiag.mp hxy
    have hxB : x ∈ B := (Finset.mem_filter.mp hx).1
    have hyB : y ∈ B := (Finset.mem_filter.mp hy).1
    apply Finset.mem_image.mpr
    refine ⟨(x, y), Finset.mem_offDiag.mpr ⟨hxB, hyB, hne⟩, rfl⟩
  have hcard_biUnion : (B.biUnion NB).card ≤ Nat.choose B.card 2 := by
    have hle : (B.biUnion NB).card ≤ (B.offDiag.image Sym2.mk.uncurry).card :=
      Finset.card_le_card hsub_all
    rw [Sym2.card_image_offDiag B] at hle
    exact hle
  have hsub_edges : B.biUnion NB ⊆ (digraph_common_predecessor_graph D).edgeFinset := by
    intro e he
    obtain ⟨u, -, heu⟩ := Finset.mem_biUnion.mp he
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp heu
    obtain ⟨hx, hy, hne⟩ := Finset.mem_offDiag.mp hxy
    have hxAdj : D.Adj u x := (Finset.mem_filter.mp hx).2
    have hyAdj : D.Adj u y := (Finset.mem_filter.mp hy).2
    rw [SimpleGraph.mem_edgeFinset]
    exact ⟨hne, ⟨u, hxAdj, hyAdj⟩⟩
  have hle_multiplicity : ∀ e ∈ B.biUnion NB,
      ((B.filter fun a => e ∈ NB a).card - 1) ≤
        ((Finset.univ.filter fun p => ∀ x, x ∈ e → D.Adj p x).card - 1) := by
    intro e he
    have hsube : (B.filter fun a => e ∈ NB a) ⊆ (Finset.univ.filter fun p => ∀ x, x ∈ e → D.Adj p x) := by
      intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      obtain ⟨-, hae⟩ := ha
      obtain ⟨⟨x, y⟩, hxy, heq⟩ := Finset.mem_image.mp hae
      obtain ⟨hx, hy, -⟩ := Finset.mem_offDiag.mp hxy
      have hxAdj : D.Adj a x := (Finset.mem_filter.mp hx).2
      have hyAdj : D.Adj a y := (Finset.mem_filter.mp hy).2
      subst heq
      intro z hz
      rcases Sym2.mem_iff.mp hz with rfl | rfl
      · exact hxAdj
      · exact hyAdj
    have := Finset.card_le_card hsube
    omega
  have hsum_le_multiplicity :
      ∑ e ∈ B.biUnion NB, ((B.filter fun a => e ∈ NB a).card - 1) ≤
        ∑ e ∈ (digraph_common_predecessor_graph D).edgeFinset,
          ((Finset.univ.filter fun p => ∀ x, x ∈ e → D.Adj p x).card - 1) := by
    have h1 : ∑ e ∈ B.biUnion NB, ((B.filter fun a => e ∈ NB a).card - 1) ≤
        ∑ e ∈ B.biUnion NB, ((Finset.univ.filter fun p => ∀ x, x ∈ e → D.Adj p x).card - 1) :=
      Finset.sum_le_sum hle_multiplicity
    have h2 : ∑ e ∈ B.biUnion NB, ((Finset.univ.filter fun p => ∀ x, x ∈ e → D.Adj p x).card - 1) ≤
        ∑ e ∈ (digraph_common_predecessor_graph D).edgeFinset,
          ((Finset.univ.filter fun p => ∀ x, x ∈ e → D.Adj p x).card - 1) :=
      Finset.sum_le_sum_of_subset hsub_edges
    exact le_trans h1 h2
  have hfamily := finite_family_overlap_multiplicity_identity α (Sym2 α) B NB
  rw [hsum_NB] at hfamily
  have hoverlap_id := digraph_common_predecessor_overlap_incidence_identity α D
  rw [← hoverlap_id]
  omega
