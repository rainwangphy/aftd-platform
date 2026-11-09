import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ChoreResidualCost
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# block_insertion_residual_cost_bound_of_gt

Topic: fair_division   Node: 401a789a0654

Provenance: helper lemma. arXiv:2611.07468 Lemma B.1

Given a type α with decidable equality, a cost function c : α → NNReal, a natural number k : ℕ with 1 ≤ k, a bundle B : Finset α with k ≤ B.card, and a bundle E : Finset α disjoint from B with k < E.card such that c e ≤ c b for all e ∈ E and b ∈ B, the k-chore residual cost chore_residual_cost c k (B ∪ E) is at most ((E.card : NNReal) / (k : NNReal)) * ∑ b ∈ B, c b.
-/

lemma block_insertion_residual_cost_bound_of_gt_aux
    (S_B_rem S_B_in S_E_rem a : NNReal) (k E_card B_inter_T_card E_sdiff_T_card : ℕ)
    (hE : E_sdiff_T_card + k = E_card + B_inter_T_card)
    (hk_le_E : k ≤ E_card)
    (hSE : S_E_rem ≤ (E_sdiff_T_card : NNReal) * a)
    (hSBin : (B_inter_T_card : NNReal) * a ≤ S_B_in)
    (hka : (k : NNReal) * a ≤ S_B_rem + S_B_in)
    (hk_pos : 0 < (k : NNReal)) :
    S_B_rem + S_E_rem ≤ ((E_card : NNReal) / (k : NNReal)) * (S_B_rem + S_B_in) := by
  have hk_ne : (k : NNReal) ≠ 0 := ne_of_gt hk_pos
  have hE_sub : E_sdiff_T_card = (E_card - k) + B_inter_T_card := by
    omega
  have hE_cast : (E_sdiff_T_card : NNReal) = ((E_card - k : ℕ) : NNReal) + (B_inter_T_card : NNReal) := by
    rw [hE_sub, Nat.cast_add]
  have h1 : S_E_rem ≤ (((E_card - k : ℕ) : NNReal) + (B_inter_T_card : NNReal)) * a := by
    rwa [← hE_cast]
  rw [add_mul] at h1
  have h2 : S_B_rem + S_E_rem ≤ (S_B_rem + S_B_in) + ((E_card - k : ℕ) : NNReal) * a := by
    calc S_B_rem + S_E_rem ≤ S_B_rem + (((E_card - k : ℕ) : NNReal) * a + (B_inter_T_card : NNReal) * a) := by gcongr
    _ = (S_B_rem + (B_inter_T_card : NNReal) * a) + ((E_card - k : ℕ) : NNReal) * a := by ring
    _ ≤ (S_B_rem + S_B_in) + ((E_card - k : ℕ) : NNReal) * a := by gcongr
  have ha_le : a ≤ (S_B_rem + S_B_in) / (k : NNReal) := by
    rw [le_div_iff₀ hk_pos, mul_comm]
    exact hka
  have h3 : ((E_card - k : ℕ) : NNReal) * a ≤ ((E_card - k : ℕ) : NNReal) * ((S_B_rem + S_B_in) / (k : NNReal)) := by
    gcongr
  have h4 : ((E_card - k : ℕ) : NNReal) * ((S_B_rem + S_B_in) / (k : NNReal)) =
    (((E_card - k : ℕ) : NNReal) / (k : NNReal)) * (S_B_rem + S_B_in) := by
    ring
  rw [h4] at h3
  have h5 : (S_B_rem + S_B_in) + ((E_card - k : ℕ) : NNReal) * a ≤
    (1 + ((E_card - k : ℕ) : NNReal) / (k : NNReal)) * (S_B_rem + S_B_in) := by
    calc (S_B_rem + S_B_in) + ((E_card - k : ℕ) : NNReal) * a
      ≤ (S_B_rem + S_B_in) + (((E_card - k : ℕ) : NNReal) / (k : NNReal)) * (S_B_rem + S_B_in) := by gcongr
      _ = (1 + ((E_card - k : ℕ) : NNReal) / (k : NNReal)) * (S_B_rem + S_B_in) := by ring
  have h6 : 1 + ((E_card - k : ℕ) : NNReal) / (k : NNReal) = (E_card : NNReal) / (k : NNReal) := by
    have : 1 = (k : NNReal) / (k : NNReal) := (div_self hk_ne).symm
    nth_rw 1 [this]
    rw [← add_div]
    congr 1
    rw [← Nat.cast_add]
    congr 1
    omega
  rw [h6] at h5
  exact h2.trans h5

/-- When |E| > k, the k-chore residual cost of B ∪ E is at most (|E| / k) * c(B). -/
theorem block_insertion_residual_cost_bound_of_gt {α : Type*} [DecidableEq α]
    (c : α → NNReal) (k : ℕ) (hk : 1 ≤ k)
    (B E : Finset α)
    (hdisj : Disjoint B E) (hkB : k ≤ B.card) (hrk : k < E.card)
    (h_cost : ∀ e ∈ E, ∀ b ∈ B, c e ≤ c b) :
    chore_residual_cost c k (B ∪ E) ≤ ((E.card : NNReal) / (k : NNReal)) * ∑ b ∈ B, c b := by
  have hk_pos : 0 < (k : NNReal) := by
    have : 0 < k := by omega
    exact Nat.cast_pos.mpr this
  have hE_nonempty : E.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h, Finset.card_empty] at hrk
    omega
  rcases Finset.exists_max_image E c hE_nonempty with ⟨e₀, he₀, he₀_max⟩
  set a := c e₀
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
  have hE_identity : (E \ T).card + k = E.card + (B ∩ T).card := by
    omega
  have hdec1 : ∑ x ∈ (B ∪ E) \ T, c x = (∑ x ∈ B \ T, c x) + ∑ x ∈ E \ T, c x := by
    rw [Finset.union_sdiff_distrib, Finset.sum_union]
    exact hdisj.mono Finset.sdiff_subset Finset.sdiff_subset
  have hdec2 : (∑ x ∈ B \ T, c x) + ∑ x ∈ B ∩ T, c x = ∑ x ∈ B, c x := by
    have := Finset.sum_sdiff (f := c) (s₁ := B ∩ T) (s₂ := B) Finset.inter_subset_left
    rw [Finset.sdiff_inter_self_left] at this
    exact this
  have hSE : ∑ x ∈ E \ T, c x ≤ ((E \ T).card : NNReal) * a := by
    calc ∑ x ∈ E \ T, c x ≤ ∑ x ∈ E \ T, a := Finset.sum_le_sum fun x hx => he₀_max x (Finset.mem_sdiff.mp hx).1
    _ = ((E \ T).card : NNReal) * a := by rw [Finset.sum_const, nsmul_eq_mul]
  have hSBin : ((B ∩ T).card : NNReal) * a ≤ ∑ x ∈ B ∩ T, c x := by
    calc ((B ∩ T).card : NNReal) * a = ∑ x ∈ B ∩ T, a := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ x ∈ B ∩ T, c x := Finset.sum_le_sum fun x hx => h_cost e₀ he₀ x (Finset.mem_inter.mp hx).1
  have hka : (k : NNReal) * a ≤ (∑ x ∈ B \ T, c x) + ∑ x ∈ B ∩ T, c x := by
    rw [hdec2]
    calc (k : NNReal) * a ≤ (B.card : NNReal) * a := by gcongr
    _ = ∑ x ∈ B, a := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ x ∈ B, c x := Finset.sum_le_sum fun x hx => h_cost e₀ he₀ x hx
  rw [hdec1, ← hdec2]
  exact block_insertion_residual_cost_bound_of_gt_aux
    (∑ x ∈ B \ T, c x) (∑ x ∈ B ∩ T, c x) (∑ x ∈ E \ T, c x) a
    k E.card (B ∩ T).card (E \ T).card
    hE_identity (by omega) hSE hSBin hka hk_pos
