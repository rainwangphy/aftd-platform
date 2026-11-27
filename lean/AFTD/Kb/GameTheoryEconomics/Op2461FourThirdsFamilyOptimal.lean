import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Op2461FourThirdsFamilyShare
import AFTD.Kb.GameTheoryEconomics.WeightedChoreMaximinShare
import AFTD.Kb.GameTheoryEconomics.Op2461FourThirdsFamilyWeight
import AFTD.Kb.GameTheoryEconomics.Op2461FourThirdsFamilyCost
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# op2461_four_thirds_family_optimal

Topic: fair_division   Node: 4ab56c6b03ee

Provenance: original. Related work: OP-2461; experiments 41658, 41660 and 41663. The two-agent 5/4 bound is in https://arxiv.org/html/2510.06581, Theorem 6.

For every positive integer r, let agents be indexed from 0 to 3r-1: the first 2r have weight one and the remaining r have weight two. Let chores be indexed from 0 to 5r-1: the first r are large, the next 2r are medium, and the last 2r are small. Every light agent assigns costs 4, 3, 1 to these chore types respectively; every heavy agent assigns costs 6, 2, 1. There exists a complete allocation with each cost at most four thirds of its weighted chore maximin share, but for every real factor strictly less than four thirds no such allocation exists. Each weighted share is the agent weight times the minimum over complete partitions of the maximum, over recipients, of that agent’s bundle cost divided by the recipient’s weight.
-/

theorem op2461_ftf_type_total (r : ℕ) (σ : Fin (5 * r) → Fin (3 * r))
    (p : Fin (5 * r) → Prop) [DecidablePred p] :
    ∑ i, ((bundle_of σ i).filter p).card = (Finset.univ.filter p).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := σ) (t := Finset.univ) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ext e
  simp [bundle_of, and_comm]

theorem op2461_four_thirds_family_optimal
    (r : ℕ) (hr : 1 ≤ r) :
    (∃ σ : Fin (5 * r) → Fin (3 * r), ∀ i,
      additive_valuation (op2461_four_thirds_family_cost r i) (bundle_of σ i) ≤
        (4 / 3 : ℝ) * weighted_chore_maximin_share (op2461_four_thirds_family_weight r)
          (op2461_four_thirds_family_cost r i) i) ∧
    ∀ α : ℝ, α < (4 / 3 : ℝ) → ¬ ∃ σ : Fin (5 * r) → Fin (3 * r), ∀ i,
      additive_valuation (op2461_four_thirds_family_cost r i) (bundle_of σ i) ≤
        α * weighted_chore_maximin_share (op2461_four_thirds_family_weight r)
          (op2461_four_thirds_family_cost r i) i := by
  constructor
  · refine ⟨op2461_ftf_partH r, fun i => ?_⟩
    have h := op2461_ftf_cost_partH r i i
    rw [op2461_four_thirds_family_share r hr i]
    split_ifs at h ⊢ <;> linarith
  · rintro α hα ⟨σ, hσ⟩
    set L : Fin (3 * r) → ℕ := fun i => ((bundle_of σ i).filter fun e => e.val < r).card with hLdef
    set M : Fin (3 * r) → ℕ := fun i =>
      ((bundle_of σ i).filter fun e => r ≤ e.val ∧ e.val < 3 * r).card with hMdef
    set S : Fin (3 * r) → ℕ := fun i =>
      ((bundle_of σ i).filter fun e => 3 * r ≤ e.val).card with hSdef
    have hbound : ∀ i, 30 * L i + 10 * M i + S i ≤ if i.val < 2 * r then 10 else 31 := by
      intro i
      have h := hσ i
      rw [op2461_four_thirds_family_share r hr i, op2461_ftf_cost_eq] at h
      by_cases hi : i.val < 2 * r
      · simp only [if_pos hi] at h ⊢
        have h4 : ((4 * L i + 3 * M i + S i : ℕ) : ℝ) < 4 := by
          push_cast; simp only [L, M, S]; linarith
        have h4' : 4 * L i + 3 * M i + S i < 4 := by exact_mod_cast h4
        have hL0 : L i = 0 := by omega
        have hM1 : M i ≤ 1 := by omega
        rw [hL0]
        interval_cases (M i) <;> omega
      · simp only [if_neg hi] at h ⊢
        have h8 : ((6 * L i + 2 * M i + S i : ℕ) : ℝ) < 8 := by
          push_cast; simp only [L, M, S]; linarith
        have h8' : 6 * L i + 2 * M i + S i < 8 := by exact_mod_cast h8
        have hL1 : L i ≤ 1 := by omega
        have hM3 : M i ≤ 3 := by omega
        interval_cases (L i) <;> interval_cases (M i) <;> omega
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hbound i)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
    have hLt : ∑ i, L i = r := by
      simp only [L]
      rw [op2461_ftf_type_total,
        op2461_ftf_card_fin_Ico (5 * r) 0 r (by omega) (by omega) _ (by intro e; omega)]
      omega
    have hMt : ∑ i, M i = 2 * r := by
      simp only [M]
      rw [op2461_ftf_type_total,
        op2461_ftf_card_fin_Ico (5 * r) r (3 * r) (by omega) (by omega) _ (by intro e; omega)]
      omega
    have hSt : ∑ i, S i = 2 * r := by
      simp only [S]
      rw [op2461_ftf_type_total,
        op2461_ftf_card_fin_Ico (5 * r) (3 * r) (5 * r) (by omega) (by omega) _
          (by intro e; have := e.isLt; omega)]
      omega
    have hB : ∑ i : Fin (3 * r), (if i.val < 2 * r then 10 else 31) = 51 * r := by
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const,
        op2461_ftf_card_fin_Ico (3 * r) 0 (2 * r) (by omega) (by omega) _ (by intro e; omega),
        op2461_ftf_card_fin_Ico (3 * r) (2 * r) (3 * r) (by omega) (by omega) _
          (by intro e; have := e.isLt; omega)]
      simp only [smul_eq_mul]
      omega
    rw [hLt, hMt, hSt, hB] at hsum
    omega
