import AFTD.Prelude
import AFTD.Kb.Tcs.RectilinearCrossingNumber

/-!
# rectilinear_crossing_number_eq_sum_powersetCard_four

Topic: combinatorics   Node: b01ecf941c3a

Provenance: helper lemma. arXiv:2610.38658 Lemma 20 -- Larger Crossing Families

The rectilinear crossing number of a finite point set P in the Euclidean plane is the sum over all 4-element subsets Q of P of the rectilinear crossing number of Q.
-/

open Classical

def rectilinear_crossing_number_eq_sum_powersetCard_four_pred
    (pair : Finset (Finset (ℝ × ℝ))) : Prop :=
  ∃ e₁ ∈ pair, ∃ e₂ ∈ pair, e₁ ≠ e₂ ∧ Disjoint e₁ e₂ ∧
  ∃ u₁ ∈ e₁, ∃ v₁ ∈ e₁, ∃ u₂ ∈ e₂, ∃ v₂ ∈ e₂, u₁ ≠ v₁ ∧ u₂ ≠ v₂ ∧
  (openSegment ℝ u₁ v₁ ∩ openSegment ℝ u₂ v₂).Nonempty

lemma rectilinear_crossing_number_eq_sum_powersetCard_four_eq_filter_card (P : Finset (ℝ × ℝ)) :
    rectilinear_crossing_number P =
      (((P.powersetCard 2).powersetCard 2).filter
        rectilinear_crossing_number_eq_sum_powersetCard_four_pred).card := by
  unfold rectilinear_crossing_number
  apply congr_arg Finset.card
  ext x
  simp [rectilinear_crossing_number_eq_sum_powersetCard_four_pred]

lemma rectilinear_crossing_number_eq_sum_powersetCard_four_biUnion_mem
    {P : Finset (ℝ × ℝ)} {pair : Finset (Finset (ℝ × ℝ))}
    (hpair : pair ∈ (P.powersetCard 2).powersetCard 2)
    (h_cross : rectilinear_crossing_number_eq_sum_powersetCard_four_pred pair) :
    pair.biUnion id ∈ P.powersetCard 4 := by
  rw [Finset.mem_powersetCard] at hpair ⊢
  rcases hpair with ⟨hpair_sub, hpair_card⟩
  have h_edges : ∀ e ∈ pair, e.card = 2 := by
    intro e he
    have := hpair_sub he
    rw [Finset.mem_powersetCard] at this
    exact this.2
  have h_edges_sub : ∀ e ∈ pair, e ⊆ P := by
    intro e he
    have := hpair_sub he
    rw [Finset.mem_powersetCard] at this
    exact this.1
  constructor
  · rw [Finset.biUnion_subset]
    exact h_edges_sub
  · rcases h_cross with ⟨e₁, he₁, e₂, he₂, hne, hdisj, _⟩
    have hpair_eq : pair = {e₁, e₂} := by
      have : {e₁, e₂} ⊆ pair := by
        rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨he₁, he₂⟩
      have hle : pair.card ≤ ({e₁, e₂} : Finset _).card := by
        rw [Finset.card_pair hne, hpair_card]
      exact (Finset.eq_of_subset_of_card_le this hle).symm
    rw [hpair_eq]
    rw [Finset.biUnion_insert, Finset.singleton_biUnion, id_eq, id_eq]
    rw [Finset.card_union_of_disjoint hdisj]
    have he1_card : e₁.card = 2 := h_edges e₁ he₁
    have he2_card : e₂.card = 2 := h_edges e₂ he₂
    rw [he1_card, he2_card]

lemma rectilinear_crossing_number_eq_sum_powersetCard_four_fiber_eq
    (P : Finset (ℝ × ℝ)) (Q : Finset (ℝ × ℝ)) (hQ : Q ∈ P.powersetCard 4) :
    {pair ∈ ((P.powersetCard 2).powersetCard 2).filter
        rectilinear_crossing_number_eq_sum_powersetCard_four_pred | pair.biUnion id = Q} =
    ((Q.powersetCard 2).powersetCard 2).filter
        rectilinear_crossing_number_eq_sum_powersetCard_four_pred := by
  rw [Finset.mem_powersetCard] at hQ
  ext pair
  rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hpairP, hcross⟩, h_union⟩
    refine ⟨?_, hcross⟩
    rw [Finset.mem_powersetCard] at hpairP ⊢
    refine ⟨?_, hpairP.2⟩
    intro e he
    rw [Finset.mem_powersetCard]
    have heP := hpairP.1 he
    rw [Finset.mem_powersetCard] at heP
    refine ⟨?_, heP.2⟩
    intro x hx
    rw [← h_union]
    exact Finset.mem_biUnion.mpr ⟨e, he, hx⟩
  · rintro ⟨hpairQ, hcross⟩
    have h_union : pair.biUnion id = Q := by
      have h_mem := rectilinear_crossing_number_eq_sum_powersetCard_four_biUnion_mem hpairQ hcross
      rw [Finset.mem_powersetCard] at h_mem
      apply Finset.eq_of_subset_of_card_le
      · exact h_mem.1
      · rw [h_mem.2, hQ.2]
    refine ⟨⟨?_, hcross⟩, h_union⟩
    rw [Finset.mem_powersetCard] at hpairQ ⊢
    refine ⟨?_, hpairQ.2⟩
    intro e he
    have heQ := hpairQ.1 he
    rw [Finset.mem_powersetCard] at heQ ⊢
    exact ⟨heQ.1.trans hQ.1, heQ.2⟩

/-- The rectilinear crossing number of P decomposes as the sum of rectilinear crossing numbers over all 4-element subsets of P. -/
theorem rectilinear_crossing_number_eq_sum_powersetCard_four
    (P : Finset (ℝ × ℝ)) :
    rectilinear_crossing_number P =
      ∑ Q ∈ P.powersetCard 4, rectilinear_crossing_number Q := by
  rw [rectilinear_crossing_number_eq_sum_powersetCard_four_eq_filter_card]
  have hmaps : Set.MapsTo (fun pair : Finset (Finset (ℝ × ℝ)) => pair.biUnion id)
      ↑(((P.powersetCard 2).powersetCard 2).filter
        rectilinear_crossing_number_eq_sum_powersetCard_four_pred)
      ↑(P.powersetCard 4) := by
    intro pair hpair
    rw [Finset.mem_coe, Finset.mem_filter] at hpair
    rw [Finset.mem_coe]
    exact rectilinear_crossing_number_eq_sum_powersetCard_four_biUnion_mem hpair.1 hpair.2
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro Q hQ
  rw [rectilinear_crossing_number_eq_sum_powersetCard_four_eq_filter_card]
  congr 1
  exact rectilinear_crossing_number_eq_sum_powersetCard_four_fiber_eq P Q hQ
