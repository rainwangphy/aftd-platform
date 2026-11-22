import AFTD.Prelude
import AFTD.Kb.Tcs.AnticompleteNeighborDefectBound
import AFTD.Kb.Tcs.BoundaryTwoExtraShoresPositiveBarrierCountImpossible
import AFTD.Kb.Tcs.FinsetCardEqSumFourBlockInter
import AFTD.Kb.Tcs.FinsetSdiffCardLeEraseSdiffCardAddOne
import AFTD.Kb.Tcs.FourDisjointSubsetsCardSumLe
import AFTD.Kb.Tcs.BoundaryFiveBlocksVertexNonneighborDefects

/-!
# boundary_five_blocks_two_extra_shores_impossible

Topic: graphs   Node: 2483a86e4b17

Provenance: helper lemma. OP-1957: graph-to-count transfer for the nonclique five-block bridge route; experiments 37129–37130 and 37135.

In the displayed degree-bounded four-block graph, a 2k-vertex residual cannot split into two endpoint shores with no cross edge except possibly xy, two nonempty mutually anticomplete extra shores also anticomplete to the endpoint shores, and a positive barrier of size at most four when the second extra shore has at least barrier size minus one vertices. The disjointness and membership assumptions are explicit.
-/

theorem boundary_five_blocks_two_extra_shores_impossible
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
    (X Y Z W S : Finset (Fin (4*k)))
    (hXY : Disjoint X Y) (hXZ : Disjoint X Z) (hXW : Disjoint X W) (hXS : Disjoint X S)
    (hYZ : Disjoint Y Z) (hYW : Disjoint Y W) (hYS : Disjoint Y S)
    (hZW : Disjoint Z W) (hZS : Disjoint Z S) (hWS : Disjoint W S)
    (hxX : x ∈ X) (hyY : y ∈ Y) (hS : 1 ≤ S.card) (hS4 : S.card ≤ 4)
    (hZ : Z.Nonempty) (hW : W.Nonempty) (hWsize : S.card ≤ W.card+1)
    (hres : (X ∪ Y ∪ Z ∪ W ∪ S).card=2*k)
    (hcross : ∀ a ∈ X, ∀ b ∈ Y, G.Adj a b → a=x ∧ b=y)
    (hantiZ : ∀ u ∈ Z, ∀ v ∈ X ∪ Y ∪ W, ¬ G.Adj u v)
    (hantiW : ∀ u ∈ W, ∀ v ∈ X ∪ Y, ¬ G.Adj u v) : False := by
  classical
  have VD := boundary_five_blocks_vertex_nonneighbor_defects k hk G A B C D hAB hCD hA hC hsizeAB hsizeCD
    hnoAB hnoCD hdegree
  have sp := fun P => finset_card_eq_sum_four_block_inter A B C D P hAB hAC hAD hBC hBD hCD hcover
  have sdi := fun P Q => Finset.card_sdiff_add_card_inter (s := (P : Finset (Fin (4*k)))) (t := Q)
  have e0 : ∀ Q : Finset (Fin (4*k)), ((∅ : Finset (Fin (4*k))) \ Q).card = 0 := by
    intro Q; simp
  have hE := fun (s : Finset (Fin (4*k))) => Finset.disjoint_empty_right s
  -- x
  have hxd := (VD x (Y.erase y) Z W ∅ (by
      intro w hw
      rcases hw with hw | hw | hw | hw
      · have hwY := Finset.mem_of_mem_erase hw
        refine ⟨fun h => Finset.disjoint_left.mp hXY (h ▸ hxX) hwY, fun h => ?_⟩
        exact Finset.ne_of_mem_erase hw (hcross x hxX w hwY h).2
      · exact ⟨fun h => Finset.disjoint_left.mp hXZ (h ▸ hxX) hw,
          fun h => hantiZ w hw x (by simp [hxX]) h.symm⟩
      · exact ⟨fun h => Finset.disjoint_left.mp hXW (h ▸ hxX) hw,
          fun h => hantiW w hw x (by simp [hxX]) h.symm⟩
      · simp at hw)
    (Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hYZ)
    (Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hYW) (hE _) hZW (hE _) (hE _)).1 hx
  -- y
  have hyd := (VD y (X.erase x) Z W ∅ (by
      intro w hw
      rcases hw with hw | hw | hw | hw
      · have hwX := Finset.mem_of_mem_erase hw
        refine ⟨fun h => Finset.disjoint_left.mp hXY (h ▸ hwX) hyY, fun h => ?_⟩
        exact Finset.ne_of_mem_erase hw (hcross w hwX y hyY h.symm).1
      · exact ⟨fun h => Finset.disjoint_left.mp hYZ (h ▸ hyY) hw,
          fun h => hantiZ w hw y (by simp [hyY]) h.symm⟩
      · exact ⟨fun h => Finset.disjoint_left.mp hYW (h ▸ hyY) hw,
          fun h => hantiW w hw y (by simp [hyY]) h.symm⟩
      · simp at hw)
    (Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hXZ)
    (Finset.disjoint_of_subset_left (Finset.erase_subset _ _) hXW) (hE _) hZW (hE _) (hE _)).2.2.1 hy
  have hx1 := finset_sdiff_card_le_erase_sdiff_card_add_one Y B y
  have hy1 := finset_sdiff_card_le_erase_sdiff_card_add_one X D x
  -- z
  obtain ⟨z, hzZ⟩ := hZ
  obtain ⟨w, hwW⟩ := hW
  have hzd := VD z X Y W ∅ (by
      intro v hv
      rcases hv with hv | hv | hv | hv
      · exact ⟨fun h => Finset.disjoint_left.mp hXZ hv (h ▸ hzZ),
          fun h => hantiZ z hzZ v (by simp [hv]) h⟩
      · exact ⟨fun h => Finset.disjoint_left.mp hYZ hv (h ▸ hzZ),
          fun h => hantiZ z hzZ v (by simp [hv]) h⟩
      · exact ⟨fun h => Finset.disjoint_left.mp hZW (h ▸ hzZ) hv,
          fun h => hantiZ z hzZ v (by simp [hv]) h⟩
      · simp at hv) hXY hXW (hE _) hYW (hE _) (hE _)
  have hwd := VD w X Y Z ∅ (by
      intro v hv
      rcases hv with hv | hv | hv | hv
      · exact ⟨fun h => Finset.disjoint_left.mp hXW hv (h ▸ hwW),
          fun h => hantiW w hwW v (by simp [hv]) h⟩
      · exact ⟨fun h => Finset.disjoint_left.mp hYW hv (h ▸ hwW),
          fun h => hantiW w hwW v (by simp [hv]) h⟩
      · exact ⟨fun h => Finset.disjoint_left.mp hZW hv (h ▸ hwW),
          fun h => hantiZ v hv w (by simp [hwW]) h.symm⟩
      · simp at hv) hXY hXZ (hE _) hYZ (hE _) (hE _)
  -- sizes
  have hun : (X ∪ Y ∪ Z ∪ W ∪ S).card = X.card + Y.card + Z.card + W.card + S.card := by
    rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint,
      Finset.card_union_of_disjoint, Finset.card_union_of_disjoint]
    · exact hXY
    · exact Finset.disjoint_union_left.mpr ⟨hXZ, hYZ⟩
    · exact Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr ⟨hXW, hYW⟩, hZW⟩
    · exact Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr
        ⟨Finset.disjoint_union_left.mpr ⟨hXS, hYS⟩, hZS⟩, hWS⟩
  have blk : ∀ Q : Finset (Fin (4*k)),
      (X ∩ Q).card + (Y ∩ Q).card + (Z ∩ Q).card + (W ∩ Q).card ≤ Q.card := by
    intro Q
    exact four_disjoint_subsets_card_sum_le _ _ _ _ Q Finset.inter_subset_right Finset.inter_subset_right
      Finset.inter_subset_right Finset.inter_subset_right
      (Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left hXY))
      (Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left hXZ))
      (Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left hXW))
      (Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left hYZ))
      (Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left hYW))
      (Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left hZW))
  have pos : ∀ (P Q : Finset (Fin (4*k))) (v : Fin (4*k)), v ∈ P → v ∈ Q → 1 ≤ (P ∩ Q).card :=
    fun P Q v h1 h2 => Finset.card_pos.mpr ⟨v, Finset.mem_inter.mpr ⟨h1, h2⟩⟩
  have hxA := pos X A x hxX hx
  have hyC := pos Y C y hyY hy
  have bA := blk A
  have bB := blk B
  have bC := blk C
  have bD := blk D
  have sX := sp X
  have sY := sp Y
  have sZ := sp Z
  have sW := sp W
  have t1 := sdi X B; have t2 := sdi Y B; have t3 := sdi Z B; have t4 := sdi W B
  have t5 := sdi X D; have t6 := sdi Y D; have t7 := sdi Z D; have t8 := sdi W D
  have t9 := sdi X A; have t10 := sdi Y A; have t11 := sdi Z A; have t12 := sdi W A
  have t13 := sdi X C; have t14 := sdi Y C; have t15 := sdi Z C; have t16 := sdi W C
  have ez := e0 A; have ez2 := e0 B; have ez3 := e0 C; have ez4 := e0 D
  have hzblk : z ∈ A ∨ z ∈ B ∨ z ∈ C ∨ z ∈ D := by
    have : z ∈ A ∪ B ∪ C ∪ D := hcover ▸ Finset.mem_univ z
    simpa [or_assoc] using this
  have hwblk : w ∈ A ∨ w ∈ B ∨ w ∈ C ∨ w ∈ D := by
    have : w ∈ A ∪ B ∪ C ∪ D := hcover ▸ Finset.mem_univ w
    simpa [or_assoc] using this
  apply boundary_two_extra_shores_positive_barrier_count_impossible k S.card
    (X ∩ A).card (X ∩ B).card (X ∩ C).card (X ∩ D).card
    (Y ∩ A).card (Y ∩ B).card (Y ∩ C).card (Y ∩ D).card
    (Z ∩ A).card (Z ∩ B).card (Z ∩ C).card (Z ∩ D).card
    (W ∩ A).card (W ∩ B).card (W ∩ C).card (W ∩ D).card hk hS hS4 hxA hyC
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · rcases hzblk with h | h | h | h
    · exact Or.inl ⟨pos Z A z hzZ h, by have := hzd.1 h; omega⟩
    · exact Or.inr (Or.inl ⟨pos Z B z hzZ h, by have := hzd.2.1 h; omega⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨pos Z C z hzZ h, by have := hzd.2.2.1 h; omega⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨pos Z D z hzZ h, by have := hzd.2.2.2 h; omega⟩))
  · rcases hwblk with h | h | h | h
    · exact Or.inl ⟨pos W A w hwW h, by have := hwd.1 h; omega⟩
    · exact Or.inr (Or.inl ⟨pos W B w hwW h, by have := hwd.2.1 h; omega⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨pos W C w hwW h, by have := hwd.2.2.1 h; omega⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨pos W D w hwW h, by have := hwd.2.2.2 h; omega⟩))
