import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ChoreResidualCost
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# block_insertion_residual_cost_bound_of_le

Topic: fair_division   Node: 99257947b1ba

Provenance: helper lemma. arXiv:2611.07468 Lemma B.1

Given a type α with decidable equality, a cost function c : α → NNReal, a natural number k : ℕ, a bundle B : Finset α with k ≤ B.card, and a bundle E : Finset α disjoint from B with E.card ≤ k such that c e ≤ c b for all e ∈ E and b ∈ B, the k-chore residual cost chore_residual_cost c k (B ∪ E) is at most ∑ b ∈ B, c b.
-/

lemma block_insertion_residual_cost_bound_of_le_sum_le_sum_of_card_le_of_le
    {α : Type*} [DecidableEq α]
    (c : α → NNReal) (s t : Finset α)
    (hcard : s.card ≤ t.card)
    (hle : ∀ x ∈ s, ∀ y ∈ t, c x ≤ c y) :
    ∑ x ∈ s, c x ≤ ∑ y ∈ t, c y := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · have ht : t.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      rintro rfl
      rw [Finset.card_empty] at hcard
      have : s.card = 0 := by omega
      exact hs.ne_empty (Finset.card_eq_zero.mp this)
    have hsc : (s.image c).Nonempty := hs.image c
    obtain ⟨x₀, hx₀, hx₀m⟩ : ∃ x ∈ s, c x = (s.image c).max' hsc := by
      have hm_mem := Finset.max'_mem (s.image c) hsc
      rcases Finset.mem_image.mp hm_mem with ⟨x₀, hx₀, heq⟩
      exact ⟨x₀, hx₀, heq⟩
    have h1 : ∑ x ∈ s, c x ≤ (s.card : NNReal) * c x₀ := by
      have : ∑ x ∈ s, c x ≤ ∑ x ∈ s, c x₀ := by
        refine Finset.sum_le_sum ?_
        intro x hx
        rw [hx₀m]
        exact Finset.le_max' (s.image c) (c x) (Finset.mem_image_of_mem c hx)
      rwa [Finset.sum_const, nsmul_eq_mul] at this
    have h2 : (t.card : NNReal) * c x₀ ≤ ∑ y ∈ t, c y := by
      have : ∑ y ∈ t, c x₀ ≤ ∑ y ∈ t, c y := by
        refine Finset.sum_le_sum ?_
        intro y hy
        exact hle x₀ hx₀ y hy
      rwa [Finset.sum_const, nsmul_eq_mul] at this
    have h3 : (s.card : NNReal) * c x₀ ≤ (t.card : NNReal) * c x₀ := by
      gcongr
    exact h1.trans (h3.trans h2)

/-- When |E| ≤ k, the k-chore residual cost of B ∪ E is at most c(B). -/
theorem block_insertion_residual_cost_bound_of_le {α : Type*} [DecidableEq α]
    (c : α → NNReal) (k : ℕ) (B E : Finset α)
    (hdisj : Disjoint B E) (hkB : k ≤ B.card) (hrk : E.card ≤ k)
    (h_cost : ∀ e ∈ E, ∀ b ∈ B, c e ≤ c b) :
    chore_residual_cost c k (B ∪ E) ≤ ∑ b ∈ B, c b := by
  unfold chore_residual_cost
  refine ciSup_le' ?_
  rintro ⟨T, hTsub, hTcard⟩
  have hkBE : k ≤ (B ∪ E).card := hkB.trans (Finset.card_le_card Finset.subset_union_left)
  have hTcard' : T.card = k := by
    rw [Nat.min_eq_left hkBE] at hTcard
    exact hTcard
  have hT_decomp : T.card = (B ∩ T).card + (E ∩ T).card := by
    have hT : T = (B ∩ T) ∪ (E ∩ T) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_inter]
      constructor
      · intro hx
        have := hTsub hx
        simp only [Finset.mem_union] at this
        rcases this with h | h
        · exact Or.inl ⟨h, hx⟩
        · exact Or.inr ⟨h, hx⟩
      · rintro (⟨-, hx⟩ | ⟨-, hx⟩) <;> exact hx
    have hd : Disjoint (B ∩ T) (E ∩ T) :=
      hdisj.mono Finset.inter_subset_left Finset.inter_subset_left
    conv_lhs => rw [hT]
    rw [Finset.card_union_of_disjoint hd]
  have hE_decomp : (E \ T).card + (E ∩ T).card = E.card :=
    Finset.card_sdiff_add_card_inter E T
  have hcard_le : (E \ T).card ≤ (B ∩ T).card := by
    omega
  have hcost_le : ∀ x ∈ E \ T, ∀ y ∈ B ∩ T, c x ≤ c y := by
    intro x hx y hy
    have hx_mem : x ∈ E := Finset.mem_sdiff.mp hx |>.1
    have hy_mem : y ∈ B := Finset.mem_inter.mp hy |>.1
    exact h_cost x hx_mem y hy_mem
  have hsum_le : ∑ x ∈ E \ T, c x ≤ ∑ x ∈ B ∩ T, c x :=
    block_insertion_residual_cost_bound_of_le_sum_le_sum_of_card_le_of_le c (E \ T) (B ∩ T) hcard_le hcost_le
  have hdec1 : ∑ x ∈ (B ∪ E) \ T, c x = (∑ x ∈ B \ T, c x) + ∑ x ∈ E \ T, c x := by
    rw [Finset.union_sdiff_distrib, Finset.sum_union]
    exact hdisj.mono Finset.sdiff_subset Finset.sdiff_subset
  have hdec2 : (∑ x ∈ B \ T, c x) + ∑ x ∈ B ∩ T, c x = ∑ x ∈ B, c x := by
    have := Finset.sum_sdiff (f := c) (s₁ := B ∩ T) (s₂ := B) Finset.inter_subset_left
    rw [Finset.sdiff_inter_self_left] at this
    exact this
  rw [hdec1, ← hdec2]
  gcongr
