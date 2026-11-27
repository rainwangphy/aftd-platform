import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.WeightedChoreMaximinShare
import AFTD.Kb.GameTheoryEconomics.Op2461FourThirdsFamilyWeight
import AFTD.Kb.GameTheoryEconomics.Op2461FourThirdsFamilyCost
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.Tcs.G

/-!
# op2461_four_thirds_family_share

Topic: fair_division   Node: 87799d4c3914

Provenance: helper lemma. Exact benchmark values in the OP-2461 counterexample family; experiments 41660 and 41663.

In the explicit family, each light agent has weighted chore maximin share three and each heavy agent has share six.
-/

theorem op2461_ftf_card_fin_Ico (n a b : ℕ) (_hab : a ≤ b) (hb : b ≤ n)
    (p : Fin n → Prop) [DecidablePred p] (hp : ∀ e, p e ↔ (a ≤ e.val ∧ e.val < b)) :
    (Finset.univ.filter p).card = b - a := by
  rw [← Finset.card_map Fin.valEmbedding]
  have h : (Finset.univ.filter p).map Fin.valEmbedding = Finset.Ico a b := by
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Fin.valEmbedding_apply, Finset.mem_Ico, hp]
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro h; exact ⟨⟨x, by omega⟩, h, rfl⟩
  rw [h, Nat.card_Ico]

theorem op2461_ftf_cost_eq (r : ℕ) (i : Fin (3 * r)) (B : Finset (Fin (5 * r))) :
    additive_valuation (op2461_four_thirds_family_cost r i) B =
      (if i.val < 2 * r then (4 : ℝ) else 6) * ((B.filter fun e => e.val < r).card : ℝ) +
      (if i.val < 2 * r then (3 : ℝ) else 2) *
        ((B.filter fun e => r ≤ e.val ∧ e.val < 3 * r).card : ℝ) +
      ((B.filter fun e => 3 * r ≤ e.val).card : ℝ) := by
  unfold additive_valuation
  rw [Finset.sum_congr rfl (g := fun e =>
      (if i.val < 2 * r then (4 : ℝ) else 6) * (if e.val < r then (1 : ℝ) else 0) +
      (if i.val < 2 * r then (3 : ℝ) else 2) *
        (if r ≤ e.val ∧ e.val < 3 * r then (1 : ℝ) else 0) +
      (if 3 * r ≤ e.val then (1 : ℝ) else 0))]
  · rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      Finset.sum_boole, Finset.sum_boole, Finset.sum_boole]
  · intro e _
    unfold op2461_four_thirds_family_cost
    split_ifs <;> first | omega | norm_num

theorem op2461_ftf_total_cost (r : ℕ) (i : Fin (3 * r)) :
    additive_valuation (op2461_four_thirds_family_cost r i) Finset.univ = 12 * r := by
  rw [op2461_ftf_cost_eq]
  rw [op2461_ftf_card_fin_Ico (5 * r) 0 r (by omega) (by omega) _ (by intro e; omega),
    op2461_ftf_card_fin_Ico (5 * r) r (3 * r) (by omega) (by omega) _ (by intro e; omega),
    op2461_ftf_card_fin_Ico (5 * r) (3 * r) (5 * r) (by omega) (by omega) _
      (by intro e; have := e.isLt; omega)]
  push_cast [Nat.sub_zero, show 3 * r - r = 2 * r by omega, show 5 * r - 3 * r = 2 * r by omega]
  split_ifs <;> ring

theorem op2461_ftf_total_weight (r : ℕ) :
    ∑ j : Fin (3 * r), op2461_four_thirds_family_weight r j = 4 * r := by
  unfold op2461_four_thirds_family_weight
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const,
    op2461_ftf_card_fin_Ico (3 * r) 0 (2 * r) (by omega) (by omega) _ (by intro e; omega),
    op2461_ftf_card_fin_Ico (3 * r) (2 * r) (3 * r) (by omega) (by omega) _
      (by intro e; have := e.isLt; omega)]
  simp only [nsmul_eq_mul]
  push_cast [Nat.sub_zero, show 3 * r - 2 * r = r by omega]
  ring

theorem op2461_ftf_weight_pos (r : ℕ) (j : Fin (3 * r)) :
    0 < op2461_four_thirds_family_weight r j := by
  unfold op2461_four_thirds_family_weight; split_ifs <;> norm_num

theorem op2461_ftf_sum_bundles {m n : ℕ} (u : Fin m → ℝ) (P : Fin m → Fin n) :
    ∑ j, additive_valuation u (bundle_of P j) = additive_valuation u Finset.univ := by
  unfold additive_valuation bundle_of
  exact Finset.sum_fiberwise Finset.univ P u

/-- Partition used for the heavy row and for the 4/3 allocation. -/
def op2461_ftf_partH (r : ℕ) (e : Fin (5 * r)) : Fin (3 * r) :=
  ⟨if e.val < r then 2 * r + e.val else if e.val < 3 * r then e.val - r else e.val - 3 * r,
    by have := e.isLt; split_ifs <;> omega⟩

/-- Partition used for the light row. -/
def op2461_ftf_partL (r : ℕ) (e : Fin (5 * r)) : Fin (3 * r) :=
  ⟨if e.val < r then 2 * r + e.val else if e.val < 3 * r then e.val - r
    else 2 * r + (e.val - 3 * r) / 2,
    by have := e.isLt; split_ifs <;> omega⟩

theorem op2461_ftf_cost_partH (r : ℕ) (i j : Fin (3 * r)) :
    additive_valuation (op2461_four_thirds_family_cost r i) (bundle_of (op2461_ftf_partH r) j) ≤
      (if i.val < 2 * r then (if j.val < 2 * r then (4 : ℝ) else 4)
        else (if j.val < 2 * r then 3 else 6)) := by
  rw [op2461_ftf_cost_eq]
  have hval : ∀ e, (op2461_ftf_partH r e).val = if e.val < r then 2 * r + e.val
      else if e.val < 3 * r then e.val - r else e.val - 3 * r := fun _ => rfl
  have hmem : ∀ (p : Fin (5 * r) → Prop) [DecidablePred p] e,
      e ∈ (bundle_of (op2461_ftf_partH r) j).filter p ↔
        (op2461_ftf_partH r e).val = j.val ∧ p e := by
    intro p _ e; simp [bundle_of, Fin.ext_iff]
  by_cases hj : j.val < 2 * r
  · have hL : ((bundle_of (op2461_ftf_partH r) j).filter fun e => e.val < r).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro e he; rw [hmem, hval] at he; split_ifs at he <;> omega
    have hM : ((bundle_of (op2461_ftf_partH r) j).filter
        fun e => r ≤ e.val ∧ e.val < 3 * r).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb; rw [hmem, hval] at ha hb; ext; split_ifs at ha hb <;> omega
    have hS : ((bundle_of (op2461_ftf_partH r) j).filter
        fun e => 3 * r ≤ e.val).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb; rw [hmem, hval] at ha hb; ext; split_ifs at ha hb <;> omega
    have hM' : (((bundle_of (op2461_ftf_partH r) j).filter
        fun e => r ≤ e.val ∧ e.val < 3 * r).card : ℝ) ≤ 1 := by exact_mod_cast hM
    have hS' : (((bundle_of (op2461_ftf_partH r) j).filter
        fun e => 3 * r ≤ e.val).card : ℝ) ≤ 1 := by exact_mod_cast hS
    rw [hL]
    split_ifs <;> push_cast <;> nlinarith
  · have hL : ((bundle_of (op2461_ftf_partH r) j).filter fun e => e.val < r).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb; rw [hmem, hval] at ha hb; ext; split_ifs at ha hb <;> omega
    have hM : ((bundle_of (op2461_ftf_partH r) j).filter
        fun e => r ≤ e.val ∧ e.val < 3 * r).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro e he; rw [hmem, hval] at he; split_ifs at he <;> omega
    have hS : ((bundle_of (op2461_ftf_partH r) j).filter
        fun e => 3 * r ≤ e.val).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro e he; rw [hmem, hval] at he; have := j.isLt; split_ifs at he <;> omega
    have hL' : (((bundle_of (op2461_ftf_partH r) j).filter
        fun e => e.val < r).card : ℝ) ≤ 1 := by exact_mod_cast hL
    rw [hM, hS]
    split_ifs <;> push_cast <;> nlinarith

theorem op2461_ftf_cost_partL (r : ℕ) (i j : Fin (3 * r)) (hi : i.val < 2 * r) :
    additive_valuation (op2461_four_thirds_family_cost r i) (bundle_of (op2461_ftf_partL r) j) ≤
      (if j.val < 2 * r then (3 : ℝ) else 6) := by
  rw [op2461_ftf_cost_eq]
  have hval : ∀ e, (op2461_ftf_partL r e).val = if e.val < r then 2 * r + e.val
      else if e.val < 3 * r then e.val - r else 2 * r + (e.val - 3 * r) / 2 := fun _ => rfl
  have hmem : ∀ (p : Fin (5 * r) → Prop) [DecidablePred p] e,
      e ∈ (bundle_of (op2461_ftf_partL r) j).filter p ↔
        (op2461_ftf_partL r e).val = j.val ∧ p e := by
    intro p _ e; simp [bundle_of, Fin.ext_iff]
  rw [if_pos hi, if_pos hi]
  by_cases hj : j.val < 2 * r
  · have hL : ((bundle_of (op2461_ftf_partL r) j).filter fun e => e.val < r).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro e he; rw [hmem, hval] at he; split_ifs at he <;> omega
    have hM : ((bundle_of (op2461_ftf_partL r) j).filter
        fun e => r ≤ e.val ∧ e.val < 3 * r).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb; rw [hmem, hval] at ha hb; ext; split_ifs at ha hb <;> omega
    have hS : ((bundle_of (op2461_ftf_partL r) j).filter
        fun e => 3 * r ≤ e.val).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro e he; rw [hmem, hval] at he; split_ifs at he <;> omega
    have hM' : (((bundle_of (op2461_ftf_partL r) j).filter
        fun e => r ≤ e.val ∧ e.val < 3 * r).card : ℝ) ≤ 1 := by exact_mod_cast hM
    rw [hL, hS, if_pos hj]
    push_cast; nlinarith
  · have hL : ((bundle_of (op2461_ftf_partL r) j).filter fun e => e.val < r).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb; rw [hmem, hval] at ha hb; ext; split_ifs at ha hb <;> omega
    have hM : ((bundle_of (op2461_ftf_partL r) j).filter
        fun e => r ≤ e.val ∧ e.val < 3 * r).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro e he; rw [hmem, hval] at he; split_ifs at he <;> omega
    have hS : ((bundle_of (op2461_ftf_partL r) j).filter
        fun e => 3 * r ≤ e.val).card ≤ 2 := by
      calc _ ≤ (Finset.univ : Finset (Fin 2)).card := by
            apply Finset.card_le_card_of_injOn (fun e => (⟨e.val % 2, by omega⟩ : Fin 2))
            · intro e _; simp
            · intro a ha b hb hab
              rw [Finset.mem_coe, hmem, hval] at ha hb
              simp only [Fin.mk.injEq] at hab
              ext; split_ifs at ha hb <;> omega
        _ = 2 := by simp
    have hL' : (((bundle_of (op2461_ftf_partL r) j).filter
        fun e => e.val < r).card : ℝ) ≤ 1 := by exact_mod_cast hL
    have hS' : (((bundle_of (op2461_ftf_partL r) j).filter
        fun e => 3 * r ≤ e.val).card : ℝ) ≤ 2 := by exact_mod_cast hS
    rw [hM, if_neg hj]
    push_cast; nlinarith

theorem op2461_four_thirds_family_share
    (r : ℕ) (hr : 1 ≤ r) (i : Fin (3 * r)) :
    weighted_chore_maximin_share (op2461_four_thirds_family_weight r)
      (op2461_four_thirds_family_cost r i) i =
        if i.val < 2 * r then (3 : ℝ) else 6 := by
  have hinf : (⨅ P : Fin (5 * r) → Fin (3 * r), ⨆ j : Fin (3 * r),
      additive_valuation (op2461_four_thirds_family_cost r i) (bundle_of P j) /
        op2461_four_thirds_family_weight r j) = 3 := by
    haveI : Nonempty (Fin (3 * r)) := ⟨⟨0, by omega⟩⟩
    apply le_antisymm
    · let P := if i.val < 2 * r then op2461_ftf_partL r else op2461_ftf_partH r
      refine ciInf_le_of_le (Set.finite_range _).bddBelow P (ciSup_le fun j => ?_)
      rw [div_le_iff₀ (op2461_ftf_weight_pos r j)]
      by_cases hi : i.val < 2 * r
      · have h := op2461_ftf_cost_partL r i j hi
        simp only [P, if_pos hi]
        unfold op2461_four_thirds_family_weight
        split_ifs at h ⊢ <;> linarith
      · have h := op2461_ftf_cost_partH r i j
        simp only [P, if_neg hi]
        unfold op2461_four_thirds_family_weight
        rw [if_neg hi] at h
        split_ifs at h ⊢ <;> linarith
    · apply le_ciInf
      intro P
      by_contra hlt
      push_neg at hlt
      have hj : ∀ j, additive_valuation (op2461_four_thirds_family_cost r i) (bundle_of P j) <
          3 * op2461_four_thirds_family_weight r j := by
        intro j
        have := lt_of_le_of_lt (le_ciSup (Set.finite_range _).bddAbove j) hlt
        rwa [div_lt_iff₀ (op2461_ftf_weight_pos r j)] at this
      have hsum := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun j _ => hj j)
      rw [op2461_ftf_sum_bundles, op2461_ftf_total_cost, ← Finset.mul_sum,
        op2461_ftf_total_weight] at hsum
      linarith
  unfold weighted_chore_maximin_share
  rw [hinf]
  unfold op2461_four_thirds_family_weight
  split_ifs <;> norm_num
