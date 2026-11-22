import AFTD.Prelude
import AFTD.Kb.Tcs.AnticompleteNeighborDefectBound
import AFTD.Kb.Tcs.BoundaryOneBarrierCountImpossible
import AFTD.Kb.Tcs.FinsetCardEqSumFourBlockInter
import AFTD.Kb.Tcs.FinsetSdiffCardLeEraseSdiffCardAddOne
import AFTD.Kb.Tcs.FourDisjointSubsetsCardSumLe
import AFTD.Kb.Tcs.BoundaryFiveBlocksVertexNonneighborDefects

/-!
# boundary_five_blocks_single_odd_extra_shore_impossible

Topic: graphs   Node: be9cf286cf72

Provenance: helper lemma. OP-1957: graph-to-count transfer for the nonclique five-block bridge route; experiments 37129–37130 and 37135.

In the displayed degree-bounded four-block graph, a 2k-vertex residual cannot split into two endpoint shores with no cross edge except possibly xy, a third odd shore anticomplete to both, and one remaining barrier vertex. The disjointness and membership assumptions are explicit.
-/

theorem boundary_five_blocks_single_odd_extra_shore_impossible
    (k : ℕ) (hk : 5 ≤ k) (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (A B C D : Finset (Fin (4*k)))
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (hcover : A ∪ B ∪ C ∪ D = Finset.univ)
    (hA : A.card=5) (hC : C.card=5)
    (hsizeAB : A.card+B.card=2*k) (hsizeCD : C.card+D.card=2*k)
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hnoCD : ∀ c ∈ C, ∀ d ∈ D, ¬ G.Adj c d)
    (hdegree : ∀ v, 2*k+2 ≤ (G.neighborFinset v).card)
    (x y : Fin (4*k)) (hx : x ∈ A) (hy : y ∈ C)
    (X Y U S : Finset (Fin (4*k)))
    (hXY : Disjoint X Y) (hXU : Disjoint X U) (hXS : Disjoint X S)
    (hYU : Disjoint Y U) (hYS : Disjoint Y S) (hUS : Disjoint U S)
    (hxX : x ∈ X) (hyY : y ∈ Y) (hS : S.card=1)
    (hres : (X ∪ Y ∪ U ∪ S).card=2*k) (hodd : Odd U.card)
    (hcross : ∀ a ∈ X, ∀ b ∈ Y, G.Adj a b → a=x ∧ b=y)
    (hanti : ∀ u ∈ U, ∀ v ∈ X ∪ Y, ¬ G.Adj u v) : False := by
  classical
  have VD := boundary_five_blocks_vertex_nonneighbor_defects k hk G A B C D hAB hCD hA hC hsizeAB hsizeCD
    hnoAB hnoCD hdegree
  have sp := fun P => finset_card_eq_sum_four_block_inter A B C D P hAB hAC hAD hBC hBD hCD hcover
  have sdi := fun P Q => Finset.card_sdiff_add_card_inter (s := (P : Finset (Fin (4*k)))) (t := Q)
  have e0 : ∀ Q : Finset (Fin (4*k)), ((∅ : Finset (Fin (4*k))) \ Q).card = 0 := by
    intro Q; simp
  have hE := fun (s : Finset (Fin (4*k))) => Finset.disjoint_empty_right s
  have hEl := fun (s : Finset (Fin (4*k))) => Finset.disjoint_empty_left s
  have hxd := (VD x (Y.erase y) U ∅ ∅ (by
      intro w hw
      rcases hw with hw | hw | hw | hw
      · have hwY := Finset.mem_of_mem_erase hw
        refine ⟨fun h => Finset.disjoint_left.mp hXY (h ▸ hxX) hwY, fun h => ?_⟩
        exact Finset.ne_of_mem_erase hw (hcross x hxX w hwY h).2
      · exact ⟨fun h => Finset.disjoint_left.mp hXU (h ▸ hxX) hw,
          fun h => hanti w hw x (by simp [hxX]) h.symm⟩
      · simp at hw
      · simp at hw)
    (Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hYU)
    (hE _) (hE _) (hE _) (hE _) (hE _)).1 hx
  have hyd := (VD y (X.erase x) U ∅ ∅ (by
      intro w hw
      rcases hw with hw | hw | hw | hw
      · have hwX := Finset.mem_of_mem_erase hw
        refine ⟨fun h => Finset.disjoint_left.mp hXY (h ▸ hwX) hyY, fun h => ?_⟩
        exact Finset.ne_of_mem_erase hw (hcross w hwX y hyY h.symm).1
      · exact ⟨fun h => Finset.disjoint_left.mp hYU (h ▸ hyY) hw,
          fun h => hanti w hw y (by simp [hyY]) h.symm⟩
      · simp at hw
      · simp at hw)
    (Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hXU)
    (hE _) (hE _) (hE _) (hE _) (hE _)).2.2.1 hy
  have hx1 := finset_sdiff_card_le_erase_sdiff_card_add_one Y B y
  have hy1 := finset_sdiff_card_le_erase_sdiff_card_add_one X D x
  have hud : ∀ u ∈ U, _ := fun u hu => VD u X Y ∅ ∅ (by
      intro v hv
      rcases hv with hv | hv | hv | hv
      · exact ⟨fun h => Finset.disjoint_left.mp hXU hv (h ▸ hu),
          fun h => hanti u hu v (by simp [hv]) h⟩
      · exact ⟨fun h => Finset.disjoint_left.mp hYU hv (h ▸ hu),
          fun h => hanti u hu v (by simp [hv]) h⟩
      · simp at hv
      · simp at hv) hXY (hE _) (hE _) (hE _) (hE _) (hE _)
  have hun : (X ∪ Y ∪ U ∪ S).card = X.card + Y.card + U.card + S.card := by
    rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint,
      Finset.card_union_of_disjoint]
    · exact hXY
    · exact Finset.disjoint_union_left.mpr ⟨hXU, hYU⟩
    · exact Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨hXS, hYS⟩, hUS⟩
  have blk : ∀ Q : Finset (Fin (4*k)),
      (X ∩ Q).card + (Y ∩ Q).card + (U ∩ Q).card + (∅ ∩ Q : Finset (Fin (4*k))).card
        ≤ Q.card := by
    intro Q
    exact four_disjoint_subsets_card_sum_le _ _ _ _ Q Finset.inter_subset_right Finset.inter_subset_right
      Finset.inter_subset_right Finset.inter_subset_right
      (Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left hXY))
      (Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left hXU))
      (Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left (hE _)))
      (Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left hYU))
      (Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left (hE _)))
      (Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left (hE _)))
  have pos : ∀ (P Q : Finset (Fin (4*k))) (v : Fin (4*k)), v ∈ P → v ∈ Q → 1 ≤ (P ∩ Q).card :=
    fun P Q v h1 h2 => Finset.card_pos.mpr ⟨v, Finset.mem_inter.mpr ⟨h1, h2⟩⟩
  have getu : ∀ Q : Finset (Fin (4*k)), 1 ≤ (U ∩ Q).card → ∃ u ∈ U, u ∈ Q := by
    intro Q h
    obtain ⟨u, hu⟩ := Finset.card_pos.mp h
    exact ⟨u, (Finset.mem_inter.mp hu).1, (Finset.mem_inter.mp hu).2⟩
  have hxA := pos X A x hxX hx
  have hyC := pos Y C y hyY hy
  have bA := blk A
  have bB := blk B
  have bC := blk C
  have bD := blk D
  have sX := sp X
  have sY := sp Y
  have sU := sp U
  have t1 := sdi X B; have t2 := sdi Y B
  have t5 := sdi X D; have t6 := sdi Y D
  have t9 := sdi X A; have t10 := sdi Y A
  have t13 := sdi X C; have t14 := sdi Y C
  have t3 := sdi U B; have t7 := sdi U D
  have ez := e0 A; have ez2 := e0 B; have ez3 := e0 C; have ez4 := e0 D
  simp only [Finset.empty_inter, Finset.card_empty, add_zero] at bA bB bC bD
  obtain ⟨t, ht⟩ := hodd
  apply boundary_one_barrier_count_impossible k
    (X ∩ A).card (X ∩ B).card (X ∩ C).card (X ∩ D).card
    (Y ∩ A).card (Y ∩ B).card (Y ∩ C).card (Y ∩ D).card
    (U ∩ A).card (U ∩ B).card (U ∩ C).card (U ∩ D).card t hk hxA hyC
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)
  · intro h; obtain ⟨u, hu, huQ⟩ := getu A h; have := (hud u hu).1 huQ; omega
  · intro h; obtain ⟨u, hu, huQ⟩ := getu B h; have := (hud u hu).2.1 huQ; omega
  · intro h; obtain ⟨u, hu, huQ⟩ := getu C h; have := (hud u hu).2.2.1 huQ; omega
  · intro h; obtain ⟨u, hu, huQ⟩ := getu D h; have := (hud u hu).2.2.2 huQ; omega
