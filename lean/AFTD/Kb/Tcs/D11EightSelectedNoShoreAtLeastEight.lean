import AFTD.Prelude
import AFTD.Kb.Tcs.FourShoreEvenCrossingIsContained

/-!
# d11_eight_selected_no_shore_at_least_eight

Topic: graphs   Node: 566264d6cc71

Provenance: helper lemma. OP-1957; structural subcase for the saturated-twin k=8 branch.

In the displayed degree-eleven crossing-shore relaxation with eight selected roots, a distinguished four-shore, and three or four internal opposite-shore vertices: No selected shore has eight or more vertices.
-/

theorem d11_eight_selected_no_shore_at_least_eight_sum_card_inter_comm
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : α → Finset β) (C : Finset β) :
    (∑ a ∈ A, (C ∩ B a).card) = ∑ c ∈ C, (A.filter (fun a => c ∈ B a)).card := by
  have h1 : (∑ a ∈ A, (C ∩ B a).card) = ∑ a ∈ A, ∑ c ∈ C, if c ∈ B a then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro a _
    have h : C ∩ B a = C.filter (fun c => c ∈ B a) := by
      ext c
      simp only [Finset.mem_inter, Finset.mem_filter]
    rw [h, Finset.card_filter]
  have h2 : (∑ c ∈ C, (A.filter (fun a => c ∈ B a)).card) = ∑ c ∈ C, ∑ a ∈ A, if c ∈ B a then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.card_filter]
  rw [h1, h2, Finset.sum_comm]

theorem d11_eight_selected_no_shore_at_least_eight
    {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]
    (x y : V) (hxy : x ≠ y) (S C F : Finset V) (hC : C.card = 18) (hSC : Disjoint S C)
    (hxC : x ∉ C) (hyC : y ∉ C) (hS : S.card = 10) (hF : F ⊆ C) (hFcard : F.card = 8)
    (hmax : ∀ a, (H.neighborFinset a).card ≤ 11)
    (hSxy : ∀ w ∈ S, H.Adj w x ∧ H.Adj w y) (Q W : V → Finset V)
    (hdis : ∀ z ∈ F, Disjoint (Q z) (W z))
    (hQ : ∀ z ∈ F, Q z ⊆ S ∪ C) (hW : ∀ z ∈ F, W z ⊆ S)
    (hxQ : ∀ z ∈ F, x ∉ Q z) (hyQ : ∀ z ∈ F, y ∉ Q z)
    (hsize : ∀ z ∈ F, (Q z).card + (W z).card = 12)
    (hzQ : ∀ z ∈ F, ∀ q ∈ Q z, H.Adj z q)
    (hcross : ∀ z ∈ F, ∀ q ∈ Q z, ∀ w ∈ W z, H.Adj q w)
    (hWmin : ∀ z ∈ F, 4 ≤ (W z).card) (hWeven : ∀ z ∈ F, Even (W z).card)
    (hcutrule : ∀ z ∈ F, ∀ z' ∈ F, (W z ∩ W z').Nonempty →
      (W z ∪ W z').card + (Q z ∩ Q z').card = 12 ∧ Even (W z ∩ W z').card)
    (z₀ : V) (hz₀ : z₀ ∈ F) (hz₀four : (W z₀).card = 4)
    (hinner : 3 ≤ (Q z₀ ∩ S).card ∧ (Q z₀ ∩ S).card ≤ 4) : ∀ z ∈ F, (W z).card < 8 := by
  classical
  intro z hz
  by_contra! hge
  have hQle4 : (Q z).card ≤ 4 := by
    have hs := hsize z hz
    omega
  have hQinter_ge2 : ∀ z' ∈ F, 2 ≤ (Q z ∩ Q z').card := by
    intro z' hz'
    have hunion_sub : W z ∪ W z' ⊆ S := Finset.union_subset (hW z hz) (hW z' hz')
    have hunion_card : (W z ∪ W z').card ≤ 10 := by
      have hc := Finset.card_le_card hunion_sub
      omega
    have winter_card : 2 ≤ (W z ∩ W z').card := by
      have hsum := Finset.card_union_add_card_inter (W z) (W z')
      have hmin' := hWmin z' hz'
      omega
    have hne : (W z ∩ W z').Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro he
      rw [he, Finset.card_empty] at winter_card
      omega
    have hcut := (hcutrule z hz z' hz' hne).1
    omega
  have hsum_ge16 : 16 ≤ ∑ z' ∈ F, (Q z ∩ Q z').card := by
    have h := Finset.sum_le_sum hQinter_ge2
    rw [Finset.sum_const, smul_eq_mul, hFcard] at h
    omega
  have hFq_le3 : ∀ q ∈ Q z, (F.filter (fun z' => q ∈ Q z')).card ≤ 3 := by
    intro q hqQ
    have hFq_sub : (F.filter (fun z' => q ∈ Q z')) ⊆ (H.neighborFinset q) ∩ C := by
      intro z' hz'
      have hz'F : z' ∈ F := (Finset.mem_filter.mp hz').1
      have hqQz' : q ∈ Q z' := (Finset.mem_filter.mp hz').2
      refine Finset.mem_inter.mpr ⟨?_, hF hz'F⟩
      exact (H.mem_neighborFinset q z').mpr (hzQ z' hz'F q hqQz').symm
    have hW_sub : W z ⊆ (H.neighborFinset q) ∩ S := by
      intro w hw
      refine Finset.mem_inter.mpr ⟨?_, hW z hz hw⟩
      exact (H.mem_neighborFinset q w).mpr (hcross z hz q hqQ w hw)
    have hd : Disjoint ((H.neighborFinset q) ∩ S) ((H.neighborFinset q) ∩ C) := by
      apply Finset.disjoint_left.mpr
      intro a ha hb
      exact (Finset.disjoint_left.mp hSC) (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2
    have hunion : ((H.neighborFinset q) ∩ S) ∪ ((H.neighborFinset q) ∩ C) ⊆ H.neighborFinset q := by
      intro a ha
      rcases Finset.mem_union.mp ha with ha | ha <;> exact (Finset.mem_inter.mp ha).1
    have hc := Finset.card_le_card hunion
    rw [Finset.card_union_of_disjoint hd] at hc
    have hm := hmax q
    have hWc := Finset.card_le_card hW_sub
    have hFqc := Finset.card_le_card hFq_sub
    omega
  have hsum_le12 : (∑ q ∈ Q z, (F.filter (fun z' => q ∈ Q z')).card) ≤ 12 := by
    have h := Finset.sum_le_sum hFq_le3
    rw [Finset.sum_const, smul_eq_mul] at h
    omega
  rw [d11_eight_selected_no_shore_at_least_eight_sum_card_inter_comm F Q (Q z)] at hsum_ge16
  omega
