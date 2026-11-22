import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.KExtendableEssentialEdgeUnextendibleMatching
import AFTD.Kb.Tcs.ForcedMatchingEdgeCommonNonneighborsBelowMinDegreeIsBridge
import AFTD.Kb.Tcs.KExtendableEssentialEdgeHasForcedMatchingResidual
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# k_extendable_essential_low_codegree_edge_yields_small_vertex_cut

Topic: graphs   Node: f2c7e172cff9

Provenance: helper lemma. OP-1957: vertex-cut formulation of the strict low-codegree residual bridge lemma; experiment 34826 checks a near-sharp example.

An essential graph edge of complement codegree at most one gives a vertex separator of size at most 2k+1 in a k-extendable graph of minimum degree at least 2k+2.
-/

theorem k_extendable_essential_low_codegree_edge_yields_small_vertex_cut
    (k j : ℕ) (hj : 2 ≤ j) (G : SimpleGraph (Fin (2*k+2*j))) [DecidableRel G.Adj]
    (hG : is_k_extendable G k) (hdeg : 2*k+2 ≤ G.minDegree)
    (u v : Fin (2*k+2*j)) (huv : G.Adj u v)
    (hessential : ¬ is_k_extendable (G.deleteEdges {s(u,v)}) k)
    (hcodeg : ((Finset.univ : Finset (Fin (2*k+2*j))).filter
      (fun w => (Gᶜ).Adj u w ∧ (Gᶜ).Adj v w)).card ≤ 1) :
    ∃ S A B : Finset (Fin (2*k+2*j)), S.card ≤ 2*k+1 ∧ A.Nonempty ∧ B.Nonempty ∧
      Disjoint S A ∧ Disjoint S B ∧ Disjoint A B ∧ S ∪ A ∪ B = Finset.univ ∧
      ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b := open SimpleGraph in by
  classical
  obtain ⟨R, hR, hu, hv, ⟨P, hP⟩, hforced⟩ :=
    k_extendable_essential_edge_has_forced_matching_residual (2*k+2*j) k G u v huv hG hessential
  let VR := {a : Fin (2*k+2*j) // a ∈ ({a | a ∈ R} : Set (Fin (2*k+2*j)))}
  let H := G.induce {a | a ∈ R}
  let uH : VR := ⟨u, hu⟩
  let vH : VR := ⟨v, hv⟩
  have huvH : H.Adj uH vH := huv
  have hdegH : ∀ x : VR, 2 ≤ H.degree x := by
    intro x
    have hdG : 2 * k + 2 ≤ G.degree x.1 := le_trans hdeg (minDegree_le_degree G x.1)
    have h_univ : (Finset.univ : Finset (Fin (2*k+2*j))).card = 2*k+2*j := Finset.card_fin (2*k+2*j)
    have h_diff_card : (Finset.univ \ R).card = 2 * k := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ R), h_univ]
      omega
    have h_sub : 2 ≤ (G.neighborFinset x.1 \ (Finset.univ \ R)).card := by
      have h2 : G.neighborFinset x.1 ⊆ (G.neighborFinset x.1 \ (Finset.univ \ R)) ∪ (Finset.univ \ R) := by
        intro y hy
        rw [Finset.mem_union]
        by_cases hyR : y ∈ R
        · left; simp [hy, hyR]
        · right; simp [hyR]
      have h3 := Finset.card_le_card h2
      have h4 := le_trans h3 (Finset.card_union_le (G.neighborFinset x.1 \ (Finset.univ \ R)) (Finset.univ \ R))
      rw [G.card_neighborFinset_eq_degree x.1, h_diff_card] at h4
      omega
    have hdegH_card : H.degree x = (H.neighborFinset x).card := (H.card_neighborFinset_eq_degree x).symm
    have h_inj : (H.neighborFinset x).map ⟨Subtype.val, Subtype.val_injective⟩ =
        (G.neighborFinset x.1 \ (Finset.univ \ R)) := by
      ext y
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk, Finset.mem_sdiff,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨z, hzR⟩, hzH, rfl⟩
        rw [H.neighborFinset_eq_filter] at hzH
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hzH
        change G.Adj x.1 z at hzH
        rw [G.neighborFinset_eq_filter]
        refine ⟨by simpa using hzH, ?_⟩
        simpa using hzR
      · intro ⟨hyG, hyR⟩
        rw [G.neighborFinset_eq_filter] at hyG
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hyG
        have hyR' : y ∈ ({a | a ∈ R} : Set (Fin (2*k+2*j))) := by
          exact not_not.mp hyR
        refine ⟨⟨y, hyR'⟩, ?_, rfl⟩
        rw [H.neighborFinset_eq_filter]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hyG
    rw [hdegH_card, ← Finset.card_map ⟨Subtype.val, Subtype.val_injective⟩, h_inj]
    exact h_sub
  have hPuv : ∃ P : H.Subgraph, P.IsPerfectMatching ∧ P.Adj uH vH := by
    by_cases hPuv : P.Adj uH vH
    · exact ⟨P, hP, hPuv⟩
    · exfalso
      apply hforced
      let P' : (H.deleteEdges {s(uH, vH)}).Subgraph := {
        verts := P.verts
        Adj := P.Adj
        adj_sub := by
          intro x y hxy
          rw [deleteEdges_adj]
          refine ⟨P.adj_sub hxy, ?_⟩
          intro he
          simp only [Set.mem_singleton_iff, Sym2.eq_iff] at he
          rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact hPuv hxy
          · exact hPuv hxy.symm
        edge_vert := P.edge_vert
        symm := P.symm
      }
      have hP'm : P'.IsPerfectMatching := hP
      exact ⟨P', hP'm⟩
  have hco : ({w | (Hᶜ).Adj uH w ∧ (Hᶜ).Adj vH w} : Set VR).ncard < 2 := by
    set C := {w : VR | (Hᶜ).Adj uH w ∧ (Hᶜ).Adj vH w}
    have hinj : Set.InjOn Subtype.val C := Subtype.val_injective.injOn
    have himage : Subtype.val '' C ⊆ (((Finset.univ : Finset (Fin (2*k+2*j))).filter
        (fun w => (Gᶜ).Adj u w ∧ (Gᶜ).Adj v w)) : Set (Fin (2*k+2*j))) := by
      rintro z ⟨w, hw, rfl⟩
      have hw1 : (Hᶜ).Adj uH w := hw.1
      have hw2 : (Hᶜ).Adj vH w := hw.2
      rw [Finset.mem_coe, Finset.mem_filter]
      refine ⟨Finset.mem_univ w.1, ?_⟩
      constructor
      · rw [compl_adj] at hw1 ⊢
        refine ⟨fun h => hw1.1 (Subtype.ext h), ?_⟩
        intro hadj
        exact hw1.2 hadj
      · rw [compl_adj] at hw2 ⊢
        refine ⟨fun h => hw2.1 (Subtype.ext h), ?_⟩
        intro hadj
        exact hw2.2 hadj
    have hcard : C.ncard ≤ ((Finset.univ : Finset (Fin (2*k+2*j))).filter
        (fun w => (Gᶜ).Adj u w ∧ (Gᶜ).Adj v w)).card := by
      rw [← Set.InjOn.ncard_image hinj, ← Set.ncard_coe_finset]
      exact Set.ncard_le_ncard himage (Set.toFinite _)
    change C.ncard < 2
    omega
  have hbridge : ¬ (H.deleteEdges {s(uH, vH)}).Reachable uH vH :=
    forced_matching_edge_common_nonneighbors_below_min_degree_is_bridge
      H 2 hdegH uH vH huvH hPuv hforced hco
  have hw : ∃ w : VR, w ≠ uH ∧ (H.deleteEdges {s(uH, vH)}).Reachable uH w := by
    have hcard : (H.neighborFinset uH).card = H.degree uH := H.card_neighborFinset_eq_degree uH
    have hvmem : vH ∈ H.neighborFinset uH := by
      rw [mem_neighborFinset]
      exact huvH
    have hdiff : 1 ≤ ((H.neighborFinset uH) \ {vH}).card := by
      rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr hvmem),
        Finset.card_singleton, hcard]
      have := hdegH uH
      omega
    have hpos : 0 < ((H.neighborFinset uH) \ {vH}).card := by omega
    obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_sdiff, Finset.mem_singleton] at hw
    have hwadj : H.Adj uH w := by
      have := hw.1
      rw [mem_neighborFinset] at this
      exact this
    have hne_u : w ≠ uH := hwadj.ne'
    have hne_v : w ≠ vH := hw.2
    have hne_sym : s(uH, w) ≠ s(uH, vH) := by
      intro he
      simp only [Sym2.eq_iff] at he
      rcases he with ⟨-, h⟩ | ⟨-, h⟩
      · exact hne_v h
      · exact hne_u h
    have hH'adj : (H.deleteEdges {s(uH, vH)}).Adj uH w := by
      rw [deleteEdges_adj]
      exact ⟨hwadj, by simpa using hne_sym⟩
    exact ⟨w, hne_u, Adj.reachable hH'adj⟩
  let H' := H.deleteEdges {s(uH, vH)}
  let AR : Finset VR := Finset.univ.filter (fun x => x ≠ uH ∧ H'.Reachable uH x)
  let BR : Finset VR := Finset.univ.filter (fun x => x ≠ uH ∧ ¬ H'.Reachable uH x)
  let A : Finset (Fin (2*k+2*j)) := AR.map ⟨Subtype.val, Subtype.val_injective⟩
  let B : Finset (Fin (2*k+2*j)) := BR.map ⟨Subtype.val, Subtype.val_injective⟩
  let S0 : Finset (Fin (2*k+2*j)) := Finset.univ \ R
  let S : Finset (Fin (2*k+2*j)) := S0 ∪ {u}
  have hS0_card : S0.card = 2 * k := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ R), Finset.card_fin]
    omega
  have hu_not_S0 : u ∉ S0 := by
    simp [S0, hu]
  have hS_card : S.card = 2 * k + 1 := by
    rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr hu_not_S0),
      hS0_card, Finset.card_singleton]
  have hAR_vH : vH ∈ BR := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, hbridge⟩
    intro h
    have : v = u := congrArg Subtype.val h
    exact huv.ne this.symm
  have hB_nonempty : B.Nonempty := by
    refine ⟨v, ?_⟩
    rw [Finset.mem_map]
    exact ⟨vH, hAR_vH, rfl⟩
  obtain ⟨w, hw1, hw2⟩ := hw
  have hAR_w : w ∈ AR := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hw1, hw2⟩
  have hA_nonempty : A.Nonempty := by
    refine ⟨w.1, ?_⟩
    rw [Finset.mem_map]
    exact ⟨w, hAR_w, rfl⟩
  have hA_sub_R : ∀ a ∈ A, a ∈ R := by
    rintro a ha
    rw [Finset.mem_map] at ha
    rcases ha with ⟨x, -, rfl⟩
    exact x.2
  have hB_sub_R : ∀ b ∈ B, b ∈ R := by
    rintro b hb
    rw [Finset.mem_map] at hb
    rcases hb with ⟨x, -, rfl⟩
    exact x.2
  have hu_not_A : u ∉ A := by
    intro ha
    rw [Finset.mem_map] at ha
    rcases ha with ⟨x, hx, hxu⟩
    rw [Finset.mem_filter] at hx
    apply hx.2.1
    exact Subtype.ext hxu
  have hu_not_B : u ∉ B := by
    intro hb
    rw [Finset.mem_map] at hb
    rcases hb with ⟨x, hx, hxu⟩
    rw [Finset.mem_filter] at hx
    apply hx.2.1
    exact Subtype.ext hxu
  have hdisj_SA : Disjoint S A := by
    rw [Finset.disjoint_left]
    intro x hxS hxA
    rw [Finset.mem_union, Finset.mem_singleton] at hxS
    rcases hxS with hxS0 | rfl
    · have hxR : x ∈ R := hA_sub_R x hxA
      simp [S0] at hxS0
      exact hxS0 hxR
    · exact hu_not_A hxA
  have hdisj_SB : Disjoint S B := by
    rw [Finset.disjoint_left]
    intro x hxS hxB
    rw [Finset.mem_union, Finset.mem_singleton] at hxS
    rcases hxS with hxS0 | rfl
    · have hxR : x ∈ R := hB_sub_R x hxB
      simp [S0] at hxS0
      exact hxS0 hxR
    · exact hu_not_B hxB
  have hdisj_AB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    rw [Finset.mem_map] at hxA hxB
    rcases hxA with ⟨a, ha, rfl⟩
    rcases hxB with ⟨b, hb, heq⟩
    have hab : a = b := Subtype.ext heq.symm
    subst hab
    rw [Finset.mem_filter] at ha hb
    exact hb.2.2 ha.2.2
  have h_univ : S ∪ A ∪ B = Finset.univ := by
    refine le_antisymm (Finset.subset_univ _) (fun x _ => ?_)
    by_cases hxR : x ∈ R
    · by_cases hxu : x = u
      · subst hxu
        apply Finset.mem_union_left
        apply Finset.mem_union_left
        apply Finset.mem_union_right
        simp
      · let xH : VR := ⟨x, hxR⟩
        have hxHne : xH ≠ uH := fun h => hxu (congrArg Subtype.val h)
        by_cases hr : H'.Reachable uH xH
        · apply Finset.mem_union_left
          apply Finset.mem_union_right
          rw [Finset.mem_map]
          exact ⟨xH, by simp [AR, hxHne, hr], rfl⟩
        · apply Finset.mem_union_right
          rw [Finset.mem_map]
          exact ⟨xH, by simp [BR, hxHne, hr], rfl⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      simp [S0, hxR]
  have h_no_adj : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b := by
    rintro a ha b hb hadj
    rw [Finset.mem_map] at ha hb
    rcases ha with ⟨aH, haH, rfl⟩
    rcases hb with ⟨bH, hbH, rfl⟩
    rw [Finset.mem_filter] at haH hbH
    have hHadj : H.Adj aH bH := hadj
    have hne : s(aH, bH) ≠ s(uH, vH) := by
      intro he
      simp only [Sym2.eq_iff] at he
      rcases he with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact haH.2.1 h1
      · exact hbH.2.1 h2
    have hH'adj : H'.Adj aH bH := by
      rw [deleteEdges_adj]
      exact ⟨hHadj, by simpa using hne⟩
    have hr : H'.Reachable uH bH := haH.2.2.trans (Adj.reachable hH'adj)
    exact hbH.2.2 hr
  refine ⟨S, A, B, ?_, hA_nonempty, hB_nonempty, hdisj_SA, hdisj_SB, hdisj_AB, h_univ, h_no_adj⟩
  omega
