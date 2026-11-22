import AFTD.Prelude
import AFTD.Kb.Tcs.ForcedMatchingEdgeBarrierComponentPartition
import AFTD.Kb.Tcs.BoundaryFiveBlockExtraPartCardLeFour
import AFTD.Kb.Tcs.OddComponentsSplitForPositiveBarrier
import AFTD.Kb.Tcs.BoundaryFiveBlocksSingleOddExtraShoreImpossible
import AFTD.Kb.Tcs.BoundaryFiveBlocksTwoExtraShoresImpossible
import AFTD.Kb.Tcs.SimpleGraphOddComponentsCardLeVertices

/-!
# boundary_five_blocks_forced_cross_edge_is_bridge

Topic: graphs   Node: 873341084f90

Provenance: helper lemma. OP-1957: proposed all-k forced-bridge strengthening, guided by unbounded-integer degree-count experiments 37123 and 37127–37130.

For every k at least five, in a four-block boundary partition with the two displayed opposite blocks of size five and minimum degree at least 2k+2, any forced perfect-matching cross edge in a 2k-vertex residual is a bridge of that residual. No clique, factor-criticality, connectivity or complementary-matching hypothesis is assumed.
-/

theorem boundary_five_blocks_forced_cross_edge_is_bridge
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
    (R : Finset (Fin (4*k))) (hR : R.card=2*k)
    (x y : Fin (4*k)) (hx : x ∈ A) (hy : y ∈ C) (hxy : G.Adj x y)
    (hxR : x ∈ R) (hyR : y ∈ R)
    (hP : ∃ P : (G.induce {v | v ∈ R}).Subgraph, P.IsPerfectMatching)
    (hforced : ¬ ∃ P : ((G.induce {v | v ∈ R}).deleteEdges
      {s(⟨x,hxR⟩,⟨y,hyR⟩)}).Subgraph, P.IsPerfectMatching) :
    ¬ ((G.induce {v | v ∈ R}).deleteEdges
      {s(⟨x,hxR⟩,⟨y,hyR⟩)}).Reachable ⟨x,hxR⟩ ⟨y,hyR⟩ := by
  classical
  intro hpath
  obtain ⟨S, X, Y, U, hSne, hSX, hSY, hSU, hXY, hXU, hYU, hcov, hxX, hyY, hcross,
      hanti, hodd⟩ :=
    forced_matching_edge_barrier_component_partition (G.induce {v | v ∈ R})
      ⟨x,hxR⟩ ⟨y,hyR⟩ hxy hP hforced hpath
  let ι : ↥{v | v ∈ R} ↪ Fin (4*k) := Function.Embedding.subtype _
  have hmem : ∀ (T : Finset ↥{v | v ∈ R}) (a : ↥{v | v ∈ R}), ι a ∈ T.map ι ↔ a ∈ T :=
    fun T a => Finset.mem_map' ι
  have hmem' : ∀ (T : Finset ↥{v | v ∈ R}) (b : Fin (4*k)), b ∈ T.map ι →
      ∃ a ∈ T, ι a = b := fun T b h => Finset.mem_map.mp h
  have hdis : ∀ T T' : Finset ↥{v | v ∈ R}, Disjoint T T' → Disjoint (T.map ι) (T'.map ι) :=
    fun T T' h => (Finset.disjoint_map _).mpr h
  have huniv : (Finset.univ : Finset ↥{v | v ∈ R}).card = 2*k := by
    simp [hR]
  set X' := X.map ι with hX'
  set Y' := Y.map ι with hY'
  set U' := U.map ι with hU'
  set S' := S.map ι with hS'
  have hxX' : x ∈ X' := (hmem X ⟨x,hxR⟩).mpr hxX
  have hyY' : y ∈ Y' := (hmem Y ⟨y,hyR⟩).mpr hyY
  have hcross' : ∀ a ∈ X', ∀ b ∈ Y', G.Adj a b → a = x ∧ b = y := by
    intro a ha b hb hab
    obtain ⟨a0, ha0, rfl⟩ := hmem' X a ha
    obtain ⟨b0, hb0, rfl⟩ := hmem' Y b hb
    obtain ⟨h1, h2⟩ := hcross a0 ha0 b0 hb0 hab
    exact ⟨congrArg Subtype.val h1, congrArg Subtype.val h2⟩
  have hantiU : ∀ u ∈ U', ∀ v ∈ X' ∪ Y', ¬ G.Adj u v := by
    intro u hu v hv huv
    obtain ⟨u0, hu0, rfl⟩ := hmem' U u hu
    rw [Finset.mem_union] at hv
    rcases hv with hv | hv
    · obtain ⟨v0, hv0, rfl⟩ := hmem' X v hv
      exact hanti u0 hu0 v0 (Finset.mem_union_left _ hv0) huv
    · obtain ⟨v0, hv0, rfl⟩ := hmem' Y v hv
      exact hanti u0 hu0 v0 (Finset.mem_union_right _ hv0) huv
  have hxU' : x ∉ U' := fun h => Finset.disjoint_left.mp (hdis X U hXU) hxX' h
  have hyU' : y ∉ U' := fun h => Finset.disjoint_left.mp (hdis Y U hYU) hyY' h
  have hU4 : U'.card ≤ 4 := boundary_five_block_extra_part_card_le_four k hk G A B C D
    hAB hCD hBD hA hC hsizeAB hsizeCD hnoAB hnoCD hdegree x y hx hy U' hxU' hyU'
    (fun u hu h => hantiU u hu x (Finset.mem_union_left _ hxX') h.symm)
    (fun u hu h => hantiU u hu y (Finset.mem_union_right _ hyY') h.symm)
  have hUcard : U'.card = U.card := Finset.card_map _
  have hs1 : 1 ≤ S.card := Finset.card_pos.mpr hSne
  have hcardU : Fintype.card ↥{a | a ∈ U} = U.card := by simp
  have hoddle := simple_graph_odd_components_card_le_vertices
    ((G.induce {v | v ∈ R}).induce {a | a ∈ U})
  have hS'card : S'.card = S.card := Finset.card_map _
  have hmemcov : ∀ a : ↥{v | v ∈ R}, a ∈ S ∨ a ∈ X ∨ a ∈ Y ∨ a ∈ U := by
    intro a
    have : a ∈ S ∪ X ∪ Y ∪ U := hcov ▸ Finset.mem_univ a
    simpa [or_assoc] using this
  rcases odd_components_split_for_positive_barrier _ S.card hs1 hodd with
    ⟨h1, hodd1⟩ | ⟨Z, W, hZ, hW, hZW, hZWu, hWs, hZWanti⟩
  · have hres : (X' ∪ Y' ∪ U' ∪ S').card = 2*k := by
      have e : X' ∪ Y' ∪ U' ∪ S' = (X ∪ Y ∪ U ∪ S).map ι := by
        simp only [hX', hY', hU', hS', Finset.map_union]
      have e2 : X ∪ Y ∪ U ∪ S = Finset.univ := by
        ext a; simp only [Finset.mem_union, Finset.mem_univ, iff_true]
        rcases hmemcov a with h | h | h | h <;> simp [h]
      rw [e, Finset.card_map, e2, huniv]
    exact boundary_five_blocks_single_odd_extra_shore_impossible k hk G A B C D
      hAB hAC hAD hBC hBD hCD hcover hA hC hsizeAB hsizeCD hnoAB hnoCD hdegree x y hx hy
      X' Y' U' S' (hdis _ _ hXY) (hdis _ _ hXU) (hdis _ _ hSX.symm) (hdis _ _ hYU)
      (hdis _ _ hSY.symm) (hdis _ _ hSU.symm) hxX' hyY' (by rw [hS'card]; exact h1) hres
      (by rw [hUcard, ← hcardU]; exact hodd1) hcross' hantiU
  · let ι2 : ↥{a | a ∈ U} ↪ ↥{v | v ∈ R} := Function.Embedding.subtype _
    set Z2 := Z.map ι2 with hZ2
    set W2 := W.map ι2 with hW2
    have hZ2U : Z2 ⊆ U := by
      intro a ha
      obtain ⟨a0, -, rfl⟩ := Finset.mem_map.mp ha
      exact a0.2
    have hW2U : W2 ⊆ U := by
      intro a ha
      obtain ⟨a0, -, rfl⟩ := Finset.mem_map.mp ha
      exact a0.2
    have hZW2 : Z2 ∪ W2 = U := by
      apply Finset.Subset.antisymm (Finset.union_subset hZ2U hW2U)
      intro a ha
      have : (⟨a, ha⟩ : ↥{a | a ∈ U}) ∈ Z ∪ W := hZWu ▸ Finset.mem_univ _
      rw [Finset.mem_union] at this ⊢
      rcases this with h | h
      · exact Or.inl (Finset.mem_map.mpr ⟨_, h, rfl⟩)
      · exact Or.inr (Finset.mem_map.mpr ⟨_, h, rfl⟩)
    set Z' := Z2.map ι with hZ'
    set W' := W2.map ι with hW'
    have hZ'U : Z' ⊆ U' := Finset.map_subset_map.mpr hZ2U
    have hW'U : W' ⊆ U' := Finset.map_subset_map.mpr hW2U
    have hres : (X' ∪ Y' ∪ Z' ∪ W' ∪ S').card = 2*k := by
      have e : X' ∪ Y' ∪ Z' ∪ W' ∪ S' = (X ∪ Y ∪ Z2 ∪ W2 ∪ S).map ι := by
        simp only [hX', hY', hZ', hW', hS', Finset.map_union]
      have e2 : X ∪ Y ∪ Z2 ∪ W2 ∪ S = Finset.univ := by
        ext a; simp only [Finset.mem_union, Finset.mem_univ, iff_true]
        rcases hmemcov a with h | h | h | h
        · simp [h]
        · simp [h]
        · simp [h]
        · rw [← hZW2, Finset.mem_union] at h
          rcases h with h | h <;> simp [h]
      rw [e, Finset.card_map, e2, huniv]
    have hZ2W2 : Disjoint Z2 W2 := (Finset.disjoint_map _).mpr hZW
    have hZ'W' : Disjoint Z' W' := hdis _ _ hZ2W2
    have hXU' := hdis _ _ hXU
    have hYU' := hdis _ _ hYU
    have hSU' := hdis _ _ hSU
    refine boundary_five_blocks_two_extra_shores_impossible k hk G A B C D
      hAB hAC hAD hBC hBD hCD hcover hA hC hsizeAB hsizeCD hnoAB hnoCD hdegree x y hx hy
      X' Y' Z' W' S' (hdis _ _ hXY)
      (Finset.disjoint_of_subset_right hZ'U hXU') (Finset.disjoint_of_subset_right hW'U hXU')
      (hdis _ _ hSX.symm)
      (Finset.disjoint_of_subset_right hZ'U hYU') (Finset.disjoint_of_subset_right hW'U hYU')
      (hdis _ _ hSY.symm) hZ'W'
      (Finset.disjoint_of_subset_left hZ'U hSU'.symm).symm.symm
      (Finset.disjoint_of_subset_left hW'U hSU'.symm).symm.symm
      hxX' hyY' (by rw [hS'card]; exact hs1) (by omega)
      (by simp only [hZ', Finset.map_nonempty, hZ2]; exact hZ)
      (by simp only [hW', Finset.map_nonempty, hW2]; exact hW)
      (by rw [hS'card, hW', Finset.card_map, hW2, Finset.card_map]; exact hWs)
      hres hcross' ?_ ?_
    · intro u hu v hv huv
      rw [Finset.mem_union] at hv
      rcases hv with hv | hv
      · exact hantiU u (hZ'U hu) v hv huv
      · obtain ⟨u1, hu1, rfl⟩ := Finset.mem_map.mp hu
        obtain ⟨u0, hu0, rfl⟩ := Finset.mem_map.mp hu1
        obtain ⟨v1, hv1, rfl⟩ := Finset.mem_map.mp hv
        obtain ⟨v0, hv0, rfl⟩ := Finset.mem_map.mp hv1
        exact hZWanti u0 hu0 v0 hv0 huv
    · intro u hu v hv huv
      exact hantiU u (hW'U hu) v hv huv
