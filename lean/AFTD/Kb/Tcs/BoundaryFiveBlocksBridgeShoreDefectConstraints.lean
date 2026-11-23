import AFTD.Prelude
import AFTD.Kb.Tcs.BoundaryFiveBlocksVertexNonneighborDefects
import AFTD.Kb.Tcs.FinsetCardEqSumFourBlockInter
import AFTD.Kb.Tcs.FourDisjointSubsetsCardSumLe
import AFTD.Kb.Tcs.AnticompleteNeighborDefectBound

/-!
# boundary_five_blocks_bridge_shore_defect_constraints

Topic: graphs   Node: f9df8737d27d

Provenance: helper lemma. OP-1957: graph-to-count transfer for the nonclique bridge-shore classification.

For the displayed four-block graph with min degree at least 2k+2 and disjoint even nonendpoint bridge shores, the stated block intersection counts satisfy the root budgets, representative-vertex nonneighbor budgets, sizes, parity, and the bound on opposite-block cross defects. This is a graph-to-integer transfer, with no connectivity or matching hypothesis.
-/

theorem boundary_five_blocks_bridge_shore_defect_constraints
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
    (Q W : Finset (Fin (4*k))) (hQW : Disjoint Q W)
    (hxQ : x ∉ Q) (hyQ : y ∉ Q) (hxW : x ∉ W) (hyW : y ∉ W)
    (hQeven : Even Q.card) (hWeven : Even W.card)
    (hsize : (Q ∪ W ∪ {x,y}).card = 2*k)
    (hyQadj : ∀ q ∈ Q, ¬ G.Adj y q)
    (hxWadj : ∀ w ∈ W, ¬ G.Adj x w)
    (hcross : ∀ q ∈ Q, ∀ w ∈ W, ¬ G.Adj q w)
    : let m := 2*k-5
      let r := (C.filter (fun c => ¬ G.Adj x c)).card
      let qa := (Q∩A).card; let qb := (Q∩B).card
      let qc := (Q∩C).card; let qd := (Q∩D).card
      let wa := (W∩A).card; let wb := (W∩B).card
      let wc := (W∩C).card; let wd := (W∩D).card
      let qs := Q.card; let ws := W.card
      5 ≤ m ∧ r ≤ 2 ∧ wc ≤ r ∧ qa+wa ≤ 4 ∧ qb+wb ≤ m ∧
      qc+wc ≤ 4 ∧ qd+wd ≤ m ∧ qs=qa+qb+qc+qd ∧ ws=wa+wb+wc+wd ∧
      Even qs ∧ Even ws ∧ qs+ws=m+3 ∧ wa+wd+r ≤ 2 ∧ qa+qb+qc ≤ 2 ∧
      (0<qa → wa+wc+wd+1 ≤ 2) ∧ (0<qb → wb+wc+wd+1+3 ≤ m) ∧
      (0<qc → wa+wb+wc+1 ≤ 2) ∧ (0<qd → wa+wb+wd+3 ≤ m) ∧
      (0<wa → qa+qc+qd+1 ≤ 2) ∧ (0<wb → qb+qc+qd+3 ≤ m) ∧
      (0<wc → qa+qb+qc+1 ≤ 2) ∧ (0<wd → qa+qb+qd+1+3 ≤ m) := by  classical
  dsimp only
  have hB : B.card = 2*k-5 := by omega
  have hD : D.card = 2*k-5 := by omega
  have hxy : x ≠ y := by
    intro h
    subst y
    exact Finset.disjoint_left.mp hAC hx hy
  have hxB : x ∉ B := Finset.disjoint_left.mp hAB hx
  have hxC : x ∉ C := Finset.disjoint_left.mp hAC hx
  have hxD : x ∉ D := Finset.disjoint_left.mp hAD hx
  have hyA : y ∉ A := Finset.disjoint_right.mp hAC hy
  have hyB : y ∉ B := Finset.disjoint_right.mp hBC hy
  have hyD : y ∉ D := Finset.disjoint_left.mp hCD hy
  have hQcard := finset_card_eq_sum_four_block_inter A B C D Q hAB hAC hAD hBC hBD hCD hcover
  have hWcard := finset_card_eq_sum_four_block_inter A B C D W hAB hAC hAD hBC hBD hCD hcover
  have hsQ (T : Finset (Fin (4*k))) := Finset.card_sdiff_add_card_inter Q T
  have hsW (T : Finset (Fin (4*k))) := Finset.card_sdiff_add_card_inter W T
  have hsplit : Q.card + W.card + 2 = 2*k := by
    have hp : Disjoint (Q ∪ W) ({x,y} : Finset (Fin (4*k))) := by
      apply Finset.disjoint_left.mpr
      intro v hv hs
      simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hv hs
      rcases hs with rfl | rfl <;> rcases hv with hv | hv
      exacts [hxQ hv, hxW hv, hyQ hv, hyW hv]
    rw [Finset.card_union_of_disjoint hp, Finset.card_union_of_disjoint hQW,
      Finset.card_pair hxy] at hsize
    omega
  have hcap (T : Finset (Fin (4*k))) : (Q∩T).card + (W∩T).card ≤ T.card := by
    have hd : Disjoint (Q∩T) (W∩T) :=
      Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left hQW)
    rw [← Finset.card_union_of_disjoint hd]
    exact Finset.card_le_card (Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right)
  have hcapA : (Q∩A).card + (W∩A).card ≤ 4 := by
    have hd : Disjoint (Q∩A) (W∩A) :=
      Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left hQW)
    have hsub : (Q∩A) ∪ (W∩A) ⊆ A.erase x := by
      intro v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact Finset.mem_erase.mpr ⟨fun h => hxQ (h ▸ (Finset.mem_inter.mp hv).1), (Finset.mem_inter.mp hv).2⟩
      · exact Finset.mem_erase.mpr ⟨fun h => hxW (h ▸ (Finset.mem_inter.mp hv).1), (Finset.mem_inter.mp hv).2⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hd, Finset.card_erase_of_mem hx, hA] at this
    omega
  have hcapC : (Q∩C).card + (W∩C).card ≤ 4 := by
    have hd : Disjoint (Q∩C) (W∩C) :=
      Finset.disjoint_of_subset_left Finset.inter_subset_left
        (Finset.disjoint_of_subset_right Finset.inter_subset_left hQW)
    have hsub : (Q∩C) ∪ (W∩C) ⊆ C.erase y := by
      intro v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · exact Finset.mem_erase.mpr ⟨fun h => hyQ (h ▸ (Finset.mem_inter.mp hv).1), (Finset.mem_inter.mp hv).2⟩
      · exact Finset.mem_erase.mpr ⟨fun h => hyW (h ▸ (Finset.mem_inter.mp hv).1), (Finset.mem_inter.mp hv).2⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hd, Finset.card_erase_of_mem hy, hC] at this
    omega
  have hcapB := hcap B
  have hcapD := hcap D
  let VD := boundary_five_blocks_vertex_nonneighbor_defects k hk G A B C D hAB hCD hA hC hsizeAB hsizeCD hnoAB hnoCD hdegree
  have hE := fun (T : Finset (Fin (4*k))) => Finset.disjoint_empty_right T
  have hqvd (u : Fin (4*k)) (hu : u ∈ Q) :=
    VD u W {y} ∅ ∅ (by
      intro v hv
      rcases hv with hv | hv | hv | hv
      · exact ⟨fun h => Finset.disjoint_left.mp hQW hu (h ▸ hv), hcross u hu v hv⟩
      · have he : v=y := Finset.mem_singleton.mp hv
        subst v
        exact ⟨fun h => hyQ (h ▸ hu), fun h => hyQadj u hu h.symm⟩
      · simp at hv
      · simp at hv)
      (Finset.disjoint_left.mpr (by intro v hv hs; have he : v=y := Finset.mem_singleton.mp hs; exact hyW (he ▸ hv)))
      (hE _) (hE _) (hE _) (hE _) (hE _)
  have hwvd (u : Fin (4*k)) (hu : u ∈ W) :=
    VD u Q {x} ∅ ∅ (by
      intro v hv
      rcases hv with hv | hv | hv | hv
      · exact ⟨fun h => Finset.disjoint_left.mp hQW (h ▸ hv) hu, fun h => hcross v hv u hu h.symm⟩
      · have he : v=x := Finset.mem_singleton.mp hv
        subst v
        exact ⟨fun h => hxW (h ▸ hu), fun h => hxWadj u hu h.symm⟩
      · simp at hv
      · simp at hv)
      (Finset.disjoint_left.mpr (by intro v hv hs; have he : v=x := Finset.mem_singleton.mp hs; exact hxQ (he ▸ hv)))
      (hE _) (hE _) (hE _) (hE _) (hE _)
  have getQ (T : Finset (Fin (4*k))) (h : 0 < (Q∩T).card) : ∃ u ∈ Q, u ∈ T := by
    obtain ⟨u, hu⟩ := Finset.card_pos.mp h
    exact ⟨u,(Finset.mem_inter.mp hu).1,(Finset.mem_inter.mp hu).2⟩
  have getW (T : Finset (Fin (4*k))) (h : 0 < (W∩T).card) : ∃ u ∈ W, u ∈ T := by
    obtain ⟨u, hu⟩ := Finset.card_pos.mp h
    exact ⟨u,(Finset.mem_inter.mp hu).1,(Finset.mem_inter.mp hu).2⟩
  have hybudget : (Q∩A).card+(Q∩B).card+(Q∩C).card ≤ 2 := by
    have hh := (VD y Q ∅ ∅ ∅ (by
      intro v hv
      rcases hv with hv | hv | hv | hv
      · exact ⟨fun h => hyQ (h ▸ hv), hyQadj v hv⟩
      · simp at hv
      · simp at hv
      · simp at hv) (hE _) (hE _) (hE _) (hE _) (hE _) (hE _)).2.2.1 hy
    simp only [Finset.empty_sdiff, Finset.card_empty, add_zero] at hh
    have hs := hsQ D
    omega
  have hySB : ({y} : Finset (Fin (4*k))) \ B = {y} := by
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · exact And.left
    · rintro rfl; exact ⟨rfl, hyB⟩
  have hySA : ({y} : Finset (Fin (4*k))) \ A = {y} := by
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · exact And.left
    · rintro rfl; exact ⟨rfl, hyA⟩
  have hySD : ({y} : Finset (Fin (4*k))) \ D = {y} := by
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · exact And.left
    · rintro rfl; exact ⟨rfl, hyD⟩
  have hySC : ({y} : Finset (Fin (4*k))) \ C = ∅ := by
    exact Finset.sdiff_eq_empty_iff_subset.mpr (Finset.singleton_subset_iff.mpr hy)
  have hxSB : ({x} : Finset (Fin (4*k))) \ B = {x} := by
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · exact And.left
    · rintro rfl; exact ⟨rfl, hxB⟩
  have hxSA : ({x} : Finset (Fin (4*k))) \ A = ∅ := by
    exact Finset.sdiff_eq_empty_iff_subset.mpr (Finset.singleton_subset_iff.mpr hx)
  have hxSD : ({x} : Finset (Fin (4*k))) \ D = {x} := by
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · exact And.left
    · rintro rfl; exact ⟨rfl, hxD⟩
  have hxSC : ({x} : Finset (Fin (4*k))) \ C = {x} := by
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_singleton]
    constructor
    · exact And.left
    · rintro rfl; exact ⟨rfl, hxC⟩
  have hqA : 0 < (Q∩A).card → (W∩A).card+(W∩C).card+(W∩D).card+1 ≤ 2 := by
    intro h
    obtain ⟨u,hu,hblock⟩ := getQ A h
    have hh := (hqvd u hu).1 hblock
    simp only [hySB, Finset.card_singleton, Finset.empty_sdiff, Finset.card_empty, add_zero] at hh
    have hs := hsW B
    omega

  have hqB : 0 < (Q∩B).card → (W∩B).card+(W∩C).card+(W∩D).card+1+3 ≤ 2*k-5 := by
    intro h
    obtain ⟨u,hu,hblock⟩ := getQ B h
    have hh := (hqvd u hu).2.1 hblock
    simp only [hySA, Finset.card_singleton, Finset.empty_sdiff, Finset.card_empty, add_zero] at hh
    have hs := hsW A
    omega

  have hqC : 0 < (Q∩C).card → (W∩A).card+(W∩B).card+(W∩C).card+1 ≤ 2 := by
    intro h
    obtain ⟨u,hu,hblock⟩ := getQ C h
    have hh := (hqvd u hu).2.2.1 hblock
    simp only [hySD, Finset.card_singleton, Finset.empty_sdiff, Finset.card_empty, add_zero] at hh
    have hs := hsW D
    omega

  have hqD : 0 < (Q∩D).card → (W∩A).card+(W∩B).card+(W∩D).card+3 ≤ 2*k-5 := by
    intro h
    obtain ⟨u,hu,hblock⟩ := getQ D h
    have hh := (hqvd u hu).2.2.2 hblock
    simp only [hySC, Finset.card_singleton, Finset.empty_sdiff, Finset.card_empty, add_zero] at hh
    have hs := hsW C
    omega

  have hwA : 0 < (W∩A).card → (Q∩A).card+(Q∩C).card+(Q∩D).card+1 ≤ 2 := by
    intro h
    obtain ⟨u,hu,hblock⟩ := getW A h
    have hh := (hwvd u hu).1 hblock
    simp only [hxSB, Finset.card_singleton, Finset.empty_sdiff, Finset.card_empty, add_zero] at hh
    have hs := hsQ B
    omega

  have hwB : 0 < (W∩B).card → (Q∩B).card+(Q∩C).card+(Q∩D).card+3 ≤ 2*k-5 := by
    intro h
    obtain ⟨u,hu,hblock⟩ := getW B h
    have hh := (hwvd u hu).2.1 hblock
    simp only [hxSA, Finset.card_singleton, Finset.empty_sdiff, Finset.card_empty, add_zero] at hh
    have hs := hsQ A
    omega

  have hwC : 0 < (W∩C).card → (Q∩A).card+(Q∩B).card+(Q∩C).card+1 ≤ 2 := by
    intro h
    obtain ⟨u,hu,hblock⟩ := getW C h
    have hh := (hwvd u hu).2.2.1 hblock
    simp only [hxSD, Finset.card_singleton, Finset.empty_sdiff, Finset.card_empty, add_zero] at hh
    have hs := hsQ D
    omega

  have hwD : 0 < (W∩D).card → (Q∩A).card+(Q∩B).card+(Q∩D).card+1+3 ≤ 2*k-5 := by
    intro h
    obtain ⟨u,hu,hblock⟩ := getW D h
    have hh := (hwvd u hu).2.2.2 hblock
    simp only [hxSC, Finset.card_singleton, Finset.empty_sdiff, Finset.card_empty, add_zero] at hh
    have hs := hsQ C
    omega
  let T := W ∩ A
  let U := W ∩ D
  let S := C.filter (fun c => ¬ G.Adj x c)
  have hTA : T ⊆ A := Finset.inter_subset_right
  have hUD : U ⊆ D := Finset.inter_subset_right
  have hSC : S ⊆ C := Finset.filter_subset _ _
  have hTU : Disjoint T U := Finset.disjoint_of_subset_left hTA (Finset.disjoint_of_subset_right hUD hAD)
  have hTS : Disjoint T S := Finset.disjoint_of_subset_left hTA (Finset.disjoint_of_subset_right hSC hAC)
  have hUS : Disjoint U S := Finset.disjoint_of_subset_left hUD (Finset.disjoint_of_subset_right hSC hCD.symm)
  have hTB : Disjoint T B := Finset.disjoint_of_subset_left hTA hAB
  have hUB : Disjoint U B := Finset.disjoint_of_subset_left hUD hBD.symm
  have hSB : Disjoint S B := Finset.disjoint_of_subset_left hSC hBC.symm
  have hxbudget : T.card+U.card+S.card ≤ 2 := by
    have hh := (VD x T U S ∅ (by
      intro v hv
      rcases hv with hv | hv | hv | hv
      · have hvW : v ∈ W := (Finset.mem_inter.mp hv).1
        exact ⟨fun h => hxW (h ▸ hvW), hxWadj v hvW⟩
      · have hvW : v ∈ W := (Finset.mem_inter.mp hv).1
        exact ⟨fun h => hxW (h ▸ hvW), hxWadj v hvW⟩
      · obtain ⟨hvC,hvno⟩ := Finset.mem_filter.mp hv
        exact ⟨fun h => hxC (h ▸ hvC), hvno⟩
      · simp at hv) hTU hTS (hE _) hUS (hE _) (hE _)).1 hx
    rw [Finset.sdiff_eq_self_of_disjoint hTB, Finset.sdiff_eq_self_of_disjoint hUB,
      Finset.sdiff_eq_self_of_disjoint hSB] at hh
    simpa using hh
  have hWC : (W ∩ C).card ≤ S.card := by
    apply Finset.card_le_card
    intro v hv
    exact Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp hv).2, hxWadj v (Finset.mem_inter.mp hv).1⟩
  have hxbudget' : (W∩A).card + (W∩D).card + (C.filter (fun c => ¬ G.Adj x c)).card ≤ 2 := by
    simpa [T,U,S] using hxbudget
  exact ⟨by omega, by omega, by simpa [S] using hWC, hcapA, by omega, hcapC, by omega,
    hQcard, hWcard, hQeven, hWeven, by omega, hxbudget',
    hybudget, hqA, hqB, hqC, hqD, hwA, hwB, hwC, hwD⟩
