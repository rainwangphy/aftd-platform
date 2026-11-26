import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OnlineICDecision
import AFTD.Kb.GameTheoryEconomics.IsOnlineDistortionBounded
import AFTD.Kb.GameTheoryEconomics.IcWinner
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.IcWinnerNat
import AFTD.Kb.GameTheoryEconomics.IsConsistentPseudometric
import AFTD.Kb.GameTheoryEconomics.CandidateMetricSocialCost

/-!
# op_2346_partial_asymptotic_lower_bound

Topic: social_choice   Node: 25bbbab47ca0

Provenance: formalization of a published result. Source: arXiv:2611.30683 Sec. 3.1, Prop. 3.5, Stay or Switch? Metric Distortion with Online Candidate Arrivals

Proposition 3.5: For every integer k ≥ 2 and horizon T = k * (k - 1) + 1, every deterministic online rule with distortion bound D satisfies 2*k - 1 ≤ D.
-/

private def op_2346_partial_asymptotic_lower_bound_min_order {T : ℕ} (τ : Fin T) :
    LinearOrder (Fin T) :=
  LinearOrder.lift' (fun c : Fin T => if c = τ then c.val else T + c.val) (by
    intro a b h
    change (if a = τ then a.val else T + a.val) = (if b = τ then b.val else T + b.val) at h
    by_cases ha : a = τ <;> by_cases hb : b = τ
    · rw [ha, hb]
    · rw [if_pos ha, if_neg hb] at h
      have := a.isLt
      omega
    · rw [if_neg ha, if_pos hb] at h
      have := b.isLt
      omega
    · rw [if_neg ha, if_neg hb] at h
      exact Fin.ext (by omega))

private lemma op_2346_partial_asymptotic_lower_bound_min_order_key {T : ℕ} (τ a b : Fin T) :
    (@LT.lt (Fin T) (op_2346_partial_asymptotic_lower_bound_min_order τ).toLT a b) ↔
      (if a = τ then a.val else T + a.val) < (if b = τ then b.val else T + b.val) := Iff.rfl

private lemma op_2346_partial_asymptotic_lower_bound_min_order_lt {T : ℕ} (τ : Fin T) {c : Fin T}
    (hc : c ≠ τ) :
    @LT.lt (Fin T) (op_2346_partial_asymptotic_lower_bound_min_order τ).toLT τ c := by
  rw [op_2346_partial_asymptotic_lower_bound_min_order_key, if_pos rfl, if_neg hc]
  have := τ.isLt
  omega

private lemma op_2346_partial_asymptotic_lower_bound_ic_winner_one {T : ℕ} (rule : OnlineICDecision T)
    {V : Type} [Fintype V] (prof : V → LinearOrder (Fin T)) (h1 : 1 < T) :
    ic_winner rule prof ⟨1, h1⟩ =
      if rule V ⟨1, h1⟩ (fun _ => true) then ⟨1, h1⟩ else ⟨0, by omega⟩ := by
  simp only [ic_winner, ic_winner_nat, Nat.reduceAdd]
  by_cases hb : rule V ⟨1, h1⟩ (fun _ => true) <;> simp [hb]

private lemma op_2346_partial_asymptotic_lower_bound_obstruction {T : ℕ} (rule : OnlineICDecision T)
    (D L : ℝ) (hL1 : 1 ≤ L) (k : ℕ) (hk : 0 < k) (τ y t : Fin T) (hne : y ≠ τ) (hyt : y ≤ t)
    (hwin : ic_winner rule
      (fun _ : Fin k => op_2346_partial_asymptotic_lower_bound_min_order τ) t = τ)
    (hD : is_online_distortion_bounded rule D) : L ≤ D := by
  haveI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  let φ : Fin k ⊕ Fin T → ℝ := fun x => match x with | Sum.inl _ => 0 | Sum.inr c => if c = τ then L else 1
  letI : PseudoMetricSpace (Fin k ⊕ Fin T) := PseudoMetricSpace.induced φ inferInstance
  have hL0 : (0:ℝ) ≤ L := le_trans zero_le_one hL1
  have hdist : ∀ (v : Fin k) (c : Fin T), dist (Sum.inl v) (Sum.inr c) = if c = τ then L else 1 := by
    intro v c
    show dist (φ (Sum.inl v)) (φ (Sum.inr c)) = if c = τ then L else 1
    rw [Real.dist_eq]
    by_cases h : c = τ
    · simp [φ, h, abs_of_nonneg hL0]
    · simp [φ, h]
  have hcons : is_consistent_pseudometric (Fin k) (Fin T)
      (fun _ : Fin k => op_2346_partial_asymptotic_lower_bound_min_order τ) := by
    intro v a b hab
    rw [hdist, hdist] at hab
    have hb : b = τ := by
      by_contra hbn
      rw [if_neg hbn] at hab
      by_cases ha : a = τ
      · rw [if_pos ha] at hab; linarith
      · rw [if_neg ha] at hab; exact absurd hab (lt_irrefl 1)
    have ha : a ≠ τ := by
      rintro rfl
      rw [if_pos rfl, if_pos hb] at hab
      exact absurd hab (lt_irrefl L)
    rw [hb]
    exact op_2346_partial_asymptotic_lower_bound_min_order_lt τ ha
  have hcost : ∀ c : Fin T, candidate_metric_social_cost (Fin k) c = (k:ℝ) * (if c = τ then L else 1) := by
    intro c
    show (∑ v : Fin k, dist (Sum.inl v) (Sum.inr c)) = (k:ℝ) * (if c = τ then L else 1)
    rw [Finset.sum_congr rfl (fun v _ => hdist v c)]
    simp
  have h := hD (Fin k)
    (fun _ : Fin k => op_2346_partial_asymptotic_lower_bound_min_order τ) hcons t y hyt
  rw [hwin, hcost, hcost] at h
  simp only [↓reduceIte, if_neg hne, mul_one] at h
  have hkR : (0:ℝ) < (k:ℝ) := by exact_mod_cast hk
  rw [mul_comm D (k:ℝ)] at h
  exact le_of_mul_le_mul_left h hkR

/-- Proposition 3.5: For horizon T = k(k-1)+1, any deterministic online IC rule has distortion at least 2k-1. -/
theorem op_2346_partial_asymptotic_lower_bound :
    ∀ (k : ℕ) (_hk : 2 ≤ k),
      ∀ (rule : OnlineICDecision (k * (k - 1) + 1)) (D : ℝ),
        is_online_distortion_bounded rule D → (2 * (k : ℝ) - 1) ≤ D := by
  intro k hk rule D hD
  have hk0 : 0 < k := by omega
  have hT2 : 1 < k * (k - 1) + 1 := by
    have h1 : 1 ≤ k - 1 := by omega
    have h2 : 2 * 1 ≤ k * (k - 1) := Nat.mul_le_mul hk h1
    omega
  let L : ℝ := |D| + 1
  have hL1 : 1 ≤ L := by
    have h0 : (0:ℝ) ≤ |D| := abs_nonneg D
    show 1 ≤ |D| + 1
    linarith
  have hmain : L ≤ D := by
    let c0 : Fin (k * (k - 1) + 1) := ⟨0, by omega⟩
    let c1 : Fin (k * (k - 1) + 1) := ⟨1, hT2⟩
    by_cases hb : rule (Fin k) c1 (fun _ => true)
    · have hwin : ic_winner rule
          (fun _ : Fin k => op_2346_partial_asymptotic_lower_bound_min_order c1) c1 = c1 := by
        rw [op_2346_partial_asymptotic_lower_bound_ic_winner_one rule
          (fun _ : Fin k => op_2346_partial_asymptotic_lower_bound_min_order c1) hT2]
        simp only [c1] at hb ⊢
        rw [if_pos hb]
      have hne : c0 ≠ c1 := by simp [c0, c1]
      have hyt : c0 ≤ c1 := by simp [c0, c1]
      exact op_2346_partial_asymptotic_lower_bound_obstruction rule D L hL1 k hk0 c1 c0 c1 hne hyt hwin hD
    · have hwin : ic_winner rule
          (fun _ : Fin k => op_2346_partial_asymptotic_lower_bound_min_order c0) c1 = c0 := by
        rw [op_2346_partial_asymptotic_lower_bound_ic_winner_one rule
          (fun _ : Fin k => op_2346_partial_asymptotic_lower_bound_min_order c0) hT2]
        simp only [c0] at hb ⊢
        rw [if_neg hb]
      have hne : c1 ≠ c0 := by simp [c0, c1]
      exact op_2346_partial_asymptotic_lower_bound_obstruction rule D L hL1 k hk0 c0 c1 c1 hne le_rfl hwin hD
  have hfin : |D| + 1 ≤ D := hmain
  linarith [le_abs_self D]
