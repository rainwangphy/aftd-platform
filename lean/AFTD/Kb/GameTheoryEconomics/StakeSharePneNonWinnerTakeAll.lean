import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsNonWinnerTakeAllProfile
import AFTD.Kb.GameTheoryEconomics.IsProcurementPne
import AFTD.Kb.GameTheoryEconomics.ProcurementAgentAllocation
import AFTD.Kb.GameTheoryEconomics.ProcurementAgentUtility
import AFTD.Kb.GameTheoryEconomics.ProcurementOthersBids
import AFTD.Kb.GameTheoryEconomics.ProcurementOthersBidsSum
import AFTD.Kb.GameTheoryEconomics.ProportionalShareAlloc
import AFTD.Kb.GameTheoryEconomics.ProportionalShareAllocationEq
import AFTD.Kb.GameTheoryEconomics.ProportionalSharePay
import AFTD.Kb.GameTheoryEconomics.ProportionalShareUtilityEq
import AFTD.Kb.GameTheoryEconomics.StakeSharePool

/-!
# stake_share_pne_non_winner_take_all

Topic: mechanism_design   Node: 894fadeaa484

In the stake-share mechanism with K, M > 0 and all costs at most L, every pure Nash equilibrium (with at least one agent) gives positive work to at least two agents.
-/

/-- In the stake-share mechanism every pure Nash equilibrium gives positive work to at least two agents, provided every agent's cost is at most the pool floor `L`. -/
theorem stake_share_pne_non_winner_take_all {L K M : ℝ} (hK : 0 < K) (hM : 0 < M) {n : ℕ}
    (hn : 0 < n) (c : Fin n → ℝ) (hc : ∀ i, c i ≤ L) (β : Fin n → List ℝ)
    (hβ : is_procurement_pne proportional_share_alloc
      (proportional_share_pay (stake_share_pool L K M)) c β) :
    is_non_winner_take_all_profile proportional_share_alloc β := by
  obtain ⟨hnn, hbr⟩ := hβ
  have hs : ∀ j, 0 ≤ (β j).sum := fun j => List.sum_nonneg (hnn j)
  set S := ∑ j, (β j).sum with hS
  have hoth : ∀ j, (procurement_others_bids β j).sum = S - (β j).sum :=
    procurement_others_bids_sum β
  have halloc : ∀ j, procurement_agent_allocation proportional_share_alloc (β j)
      (procurement_others_bids β j) = (β j).sum / S := by
    intro j; rw [proportional_share_allocation_eq, hoth]; ring_nf
  have hutil : ∀ j σ, procurement_agent_utility proportional_share_alloc
      (proportional_share_pay (stake_share_pool L K M)) (c j) σ (procurement_others_bids β j) =
      σ.sum / (σ.sum + (S - (β j).sum)) * (stake_share_pool L K M (σ.sum + (S - (β j).sum)) - c j) := by
    intro j σ; rw [proportional_share_utility_eq, hoth]
  by_contra hcon
  have hcon' : ∀ i j, i ≠ j → 0 < (β i).sum / S → (β j).sum / S ≤ 0 := by
    intro i j hij hi
    by_contra hj
    exact hcon ⟨i, j, hij, by rw [halloc]; exact hi, by rw [halloc]; linarith⟩
  rcases (Finset.sum_nonneg (fun j _ => hs j) : 0 ≤ S).lt_or_eq with hSpos | hSzero
  · -- some agent is active; it must be the only one
    obtain ⟨i, hi⟩ : ∃ i, 0 < (β i).sum := by
      by_contra h
      push Not at h
      have : S ≤ 0 := Finset.sum_nonpos (fun j _ => h j)
      linarith
    have hzero : ∀ j, j ≠ i → (β j).sum = 0 := by
      intro j hj
      have h1 := hcon' i j (Ne.symm hj) (div_pos hi hSpos)
      have h2 : (β j).sum ≤ 0 := by
        by_contra h3; push Not at h3; have := div_pos h3 hSpos; linarith
      linarith [hs j]
    have hSi : S = (β i).sum := by
      rw [hS, Finset.sum_eq_single i (fun j _ hj => hzero j hj) (by simp)]
    set t := min (β i).sum M / 2 with ht
    have htpos : 0 < t := by rw [ht]; exact div_pos (lt_min hi hM) two_pos
    have htle : t < (β i).sum := by
      have := min_le_left (β i).sum M; rw [ht]; linarith
    have htM : t < M := by
      have := min_le_right (β i).sum M; rw [ht]; linarith
    have hdev := hbr i [t] (by simp; linarith)
    rw [hutil, hutil, hSi, sub_self, add_zero, add_zero, List.sum_singleton,
      div_self (ne_of_gt htpos), div_self (ne_of_gt hi), one_mul, one_mul] at hdev
    unfold stake_share_pool at hdev
    rw [max_eq_right (by linarith : (0 : ℝ) ≤ M - t)] at hdev
    have : max 0 (M - (β i).sum) < M - t := by
      apply max_lt <;> linarith
    nlinarith
  · -- nobody is active: any agent profits from a small stake
    let i : Fin n := ⟨0, hn⟩
    have hall : ∀ j, (β j).sum = 0 := by
      intro j
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hs j)).mp hSzero.symm j (by simp)
      exact this
    have hdev := hbr i [M / 2] (by simp; linarith)
    have hS0 : S = 0 := hSzero.symm
    rw [hutil, hutil, hS0, hall i, sub_zero, add_zero, add_zero, List.sum_singleton,
      div_self (by linarith : M / 2 ≠ 0), one_mul, zero_div, zero_mul] at hdev
    unfold stake_share_pool at hdev
    rw [max_eq_right (by linarith : (0 : ℝ) ≤ M - M / 2)] at hdev
    have := hc i
    nlinarith
