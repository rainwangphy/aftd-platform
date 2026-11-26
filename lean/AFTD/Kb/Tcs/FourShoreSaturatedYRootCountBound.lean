import AFTD.Prelude
import AFTD.Kb.Tcs.AnticompleteNeighborDefectBound
import AFTD.Kb.Tcs.FinsetCardEqSumFourBlockInter
import AFTD.Kb.Tcs.Op1957EndpointResidualNonneighborBudget

/-!
# four_shore_saturated_y_root_count_bound

Topic: graphs   Node: 946d3d889a30

Provenance: helper lemma. OP-1957; positive-separator graph-to-count root degree transfer.

Under the displayed four-shore and block-disjointness assumptions, the degree of y forces the listed root count inequality.
-/

set_option maxHeartbeats 2000000

theorem four_shore_saturated_y_root_count_bound
    (k c : ℕ) (hc : 7 ≤ c) (hkc : c ≤ k)
    (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (A B C D E : Finset (Fin (4*k))) (F : Fin 4 → Finset (Fin (4*k)))
    (x y : Fin (4*k))
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (hcover : A ∪ B ∪ C ∪ D = Finset.univ)
    (hFdis : ∀ i j, i ≠ j → Disjoint (F i) (F j))
    (hEdis : ∀ i, Disjoint (F i) E) (hEB : E ⊆ B)
    (h2A : Disjoint (F 2) A) (h2D : Disjoint (F 2) D)
    (h3A : Disjoint (F 3) A) (h3D : Disjoint (F 3) D)
    (hxA : x ∈ A) (hxF : x ∈ F 0) (hyC : y ∈ C) (hyF : y ∈ F 1)
    (hD : D.card=2*k-c)
    (hcross : ∀ i j : Fin 4, i ≠ j → ∀ a ∈ F i, ∀ b ∈ F j, G.Adj a b →
      (i=0 ∧ j=1 ∧ a=x ∧ b=y) ∨ (i=1 ∧ j=0 ∧ a=y ∧ b=x))
    (hEanti : ∀ i, ∀ a ∈ F i, ∀ b ∈ E, ¬ G.Adj a b)
    (hnoCD : ∀ a ∈ C, ∀ b ∈ D, ¬ G.Adj a b)
    (hdegree : 2*k+2 ≤ (G.neighborFinset y).card) :
    (F 0 ∩ A).card+(F 0 ∩ B).card+(F 0 ∩ C).card+
      (F 2 ∩ B).card+(F 2 ∩ C).card+(F 3 ∩ B).card+(F 3 ∩ C).card+
      E.card+2 ≤ c := by
  classical
  let U := F 2 ∪ F 3 ∪ E
  have h0U : Disjoint (F 0) U := Finset.disjoint_union_right.mpr
    ⟨Finset.disjoint_union_right.mpr ⟨hFdis 0 2 (by decide),hFdis 0 3 (by decide)⟩,hEdis 0⟩
  have h1U : Disjoint (F 1) U := Finset.disjoint_union_right.mpr
    ⟨Finset.disjoint_union_right.mpr ⟨hFdis 1 2 (by decide),hFdis 1 3 (by decide)⟩,hEdis 1⟩
  have hUD : Disjoint U D := Finset.disjoint_union_left.mpr
    ⟨Finset.disjoint_union_left.mpr ⟨h2D,h3D⟩,Finset.disjoint_of_subset_left hEB hBD⟩
  have hyD : y ∉ D := fun h => Finset.disjoint_left.mp hCD hyC h
  have hnoU : ∀ u ∈ U, ¬ G.Adj y u := by
    intro u hu hadj
    rcases Finset.mem_union.mp hu with hu23 | huE
    · rcases Finset.mem_union.mp hu23 with hu2 | hu3
      · have hh := hcross 1 2 (by decide) y hyF u hu2 hadj
        simp at hh
      · have hh := hcross 1 3 (by decide) y hyF u hu3 hadj
        simp at hh
    · exact hEanti 1 y hyF u huE hadj
  have hxy : ∀ a ∈ F 0, ∀ b ∈ F 1, G.Adj a b → a=x ∧ b=y := by
    intro a ha b hb hadj
    have hh := hcross 0 1 (by decide) a ha b hb hadj
    simpa using hh
  have hroot := op1957_endpoint_residual_nonneighbor_budget k c hc hkc G (F 0) (F 1) U D x y
    (hFdis 0 1 (by decide)) h0U h1U hUD hxF hyF hyD hD hxy hnoU
    (fun v hv => hnoCD y hyC v hv) hdegree
  have h0sum := finset_card_eq_sum_four_block_inter A B C D (F 0)
    hAB hAC hAD hBC hBD hCD hcover
  have h2sum := finset_card_eq_sum_four_block_inter A B C D (F 2)
    hAB hAC hAD hBC hBD hCD hcover
  have h3sum := finset_card_eq_sum_four_block_inter A B C D (F 3)
    hAB hAC hAD hBC hBD hCD hcover
  have h2A0 : F 2 ∩ A = ∅ := Finset.disjoint_iff_inter_eq_empty.mp h2A
  have h2D0 : F 2 ∩ D = ∅ := Finset.disjoint_iff_inter_eq_empty.mp h2D
  have h3A0 : F 3 ∩ A = ∅ := Finset.disjoint_iff_inter_eq_empty.mp h3A
  have h3D0 : F 3 ∩ D = ∅ := Finset.disjoint_iff_inter_eq_empty.mp h3D
  rw [h2A0,h2D0] at h2sum
  rw [h3A0,h3D0] at h3sum
  simp only [Finset.card_empty,zero_add,add_zero] at h2sum h3sum
  have h23E : Disjoint (F 2 ∪ F 3) E := Finset.disjoint_union_left.mpr ⟨hEdis 2,hEdis 3⟩
  have hUcard : U.card = (F 2).card+(F 3).card+E.card := by
    dsimp [U]
    rw [Finset.card_union_of_disjoint h23E,Finset.card_union_of_disjoint (hFdis 2 3 (by decide))]
  have hxD : x ∉ D := fun h => Finset.disjoint_left.mp hAD hxA h
  have hx0D : x ∈ F 0 \ D := Finset.mem_sdiff.mpr ⟨hxF,hxD⟩
  have herase : ((F 0).erase x) \ D = (F 0 \ D).erase x := by
    ext z
    simp [and_comm, and_left_comm, and_assoc]
  have h0count : (((F 0).erase x) \ D).card+1 =
      (F 0 ∩ A).card+(F 0 ∩ B).card+(F 0 ∩ C).card := by
    rw [herase,Finset.card_erase_add_one hx0D]
    have hh := Finset.card_sdiff_add_card_inter (F 0) D
    omega
  omega
