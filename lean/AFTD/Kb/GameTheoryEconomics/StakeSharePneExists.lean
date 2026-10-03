import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsProcurementPne
import AFTD.Kb.GameTheoryEconomics.ProcurementOthersBidsSum
import AFTD.Kb.GameTheoryEconomics.ProportionalShareAlloc
import AFTD.Kb.GameTheoryEconomics.ProportionalSharePay
import AFTD.Kb.GameTheoryEconomics.ProportionalShareUtilityEq
import AFTD.Kb.GameTheoryEconomics.StakeShareBestResponse
import AFTD.Kb.GameTheoryEconomics.StakeSharePool

/-!
# stake_share_pne_exists

Topic: mechanism_design   Node: 776de5e370e8

For n >= 2 agents with costs in [0, L], if K M >= 3 n^2 L then the stake-share mechanism has a pure Nash equilibrium (each agent submitting a single stake).
-/

/-- For any number `n ≥ 2` of agents with costs in `[0, L]`, once `K * M ≥ 3 n² L` the stake-share mechanism has a pure Nash equilibrium (in single bids). -/
theorem stake_share_pne_exists {n : ℕ} (hn : 2 ≤ n) {L K M : ℝ} (hL : 0 ≤ L) (hK : 0 < K)
    (hM : 0 < M) (hKM : 3 * (n : ℝ) ^ 2 * L ≤ K * M) (c : Fin n → ℝ)
    (hc : ∀ i, 0 ≤ c i ∧ c i ≤ L) :
    ∃ β : Fin n → List ℝ, is_procurement_pne proportional_share_alloc
      (proportional_share_pay (stake_share_pool L K M)) c β := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set D := K * M with hDdef
  have hD : 0 < D := mul_pos hK hM
  set A : Fin n → ℝ := fun i => L - c i + D with hAdef
  have hA_lo : ∀ i, D ≤ A i := fun i => by simp only [hAdef]; linarith [(hc i).2]
  have hA_hi : ∀ i, A i ≤ D + L := fun i => by simp only [hAdef]; linarith [(hc i).1]
  have hA_pos : ∀ i, 0 < A i := fun i => lt_of_lt_of_le hD (hA_lo i)
  set H := ∑ j, 1 / A j with hHdef
  have hH_lo : (n : ℝ) / (D + L) ≤ H := by
    have h : ∑ _j : Fin n, 1 / (D + L) ≤ H :=
      Finset.sum_le_sum (fun j _ => one_div_le_one_div_of_le (hA_pos j) (hA_hi j))
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
    rw [div_eq_mul_one_div]; exact h
  have hDL : 0 < D + L := by linarith
  have hH_pos : 0 < H := lt_of_lt_of_le (div_pos (by linarith) hDL) hH_lo
  set W := ((n : ℝ) - 1) / (K * H) with hWdef
  have hW : 0 < W := div_pos (by linarith) (mul_pos hK hH_pos)
  have hKW : K * W = ((n : ℝ) - 1) / H := by
    rw [hWdef]; field_simp
  have hKWH : K * W * H = (n : ℝ) - 1 := by rw [hKW]; field_simp
  -- `K W ≤ (n - 1)(D + L)/n ≤ D`
  have hKW_le : K * W ≤ ((n : ℝ) - 1) * (D + L) / n := by
    rw [hKW, div_le_iff₀ hH_pos]
    have h1 : ((n : ℝ) - 1) * (D + L) / n * ((n : ℝ) / (D + L)) = (n : ℝ) - 1 := by
      field_simp
    have h2 : 0 ≤ ((n : ℝ) - 1) * (D + L) / n :=
      div_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hH_lo h2]
  have hnL : ((n : ℝ) - 1) * L ≤ D := by nlinarith
  have hKW_D : K * W ≤ D := by
    refine hKW_le.trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hWM : W ≤ M := by
    have : K * W ≤ K * M := hKW_D
    exact le_of_mul_le_mul_left this hK
  set s : Fin n → ℝ := fun i => W - K * W ^ 2 / A i with hsdef
  have hR_nonneg : ∀ i, 0 ≤ K * W ^ 2 / A i := fun i => by
    have := hA_pos i; positivity
  have hR_le : ∀ i, K * W ^ 2 / A i ≤ W := fun i => by
    rw [div_le_iff₀ (hA_pos i)]
    have : K * W ≤ A i := hKW_D.trans (hA_lo i)
    nlinarith
  have hsum : ∑ j, s j = W := by
    simp only [hsdef]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : ∑ j, K * W ^ 2 / A j = K * W * H * W := by
      rw [hHdef, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [this, hKWH]; ring
  refine ⟨fun i => [s i], ⟨fun i b hb => ?_, fun i σ hσ => ?_⟩⟩
  · simp only [List.mem_singleton] at hb
    rw [hb]; simp only [hsdef]; linarith [hR_le i]
  · have hσs : 0 ≤ σ.sum := List.sum_nonneg hσ
    rw [proportional_share_utility_eq, proportional_share_utility_eq, procurement_others_bids_sum]
    simp only [List.sum_singleton]
    rw [hsum]
    have hsi : s i = W - K * W ^ 2 / A i := rfl
    have hR : W - s i = K * W ^ 2 / A i := by rw [hsi]; ring
    rw [hR, show s i + K * W ^ 2 / A i = W by rw [hsi]; ring, hsi]
    apply stake_share_best_response hK (hc i).2 (hR_nonneg i) hW hWM _ _ hσs
    · show A i * (K * W ^ 2 / A i) = K * W ^ 2
      exact mul_div_cancel₀ _ (hA_pos i).ne'
    · -- the equilibrium utility is at least the payoff `L - c i` of an unbounded stake
      rw [max_eq_right (sub_nonneg.2 hWM)]
      have hAi := hA_pos i
      have hlin : L + K * (M - W) - c i = A i - K * W := by
        simp only [hAdef, hDdef]; ring
      have e : (W - K * W ^ 2 / A i) / W * (A i - K * W) = (A i - K * W) ^ 2 / A i := by
        field_simp
      rw [hlin, e, le_div_iff₀ hAi]
      have npos : (0 : ℝ) < n := by linarith
      set g := (D - ((n : ℝ) - 1) * L) / n with hg
      have hng : (n : ℝ) * g = D - ((n : ℝ) - 1) * L := by
        rw [hg]; exact mul_div_cancel₀ _ npos.ne'
      have hg_ge : 2 * n * L ≤ g := by
        have hq : 0 ≤ ((n : ℝ) ^ 2 - n + 1) * L := mul_nonneg (by nlinarith) hL
        have : (n : ℝ) * (2 * n * L) ≤ n * g := by rw [hng]; linear_combination hKM + hq
        exact le_of_mul_le_mul_left this npos
      have hnKW : (n : ℝ) * (K * W) ≤ ((n : ℝ) - 1) * (D + L) := by
        have := mul_le_mul_of_nonneg_left hKW_le npos.le
        rwa [mul_div_cancel₀ _ npos.ne'] at this
      have hgap : g ≤ A i - K * W := by
        have hA' : (n : ℝ) * D ≤ n * A i := mul_le_mul_of_nonneg_left (hA_lo i) npos.le
        have : (n : ℝ) * g ≤ n * (A i - K * W) := by
          rw [hng]; linear_combination hA' + hnKW
        exact le_of_mul_le_mul_left this npos
      have hg0 : 0 ≤ g := le_trans (by positivity) hg_ge
      have hsq : g ^ 2 ≤ (A i - K * W) ^ 2 := pow_le_pow_left₀ hg0 hgap 2
      have hci := hc i
      have i1 : 2 * n * L * g ≤ g * g := mul_le_mul_of_nonneg_right hg_ge hg0
      have i2 : 2 * n * L * (2 * n * L) ≤ 2 * n * L * g :=
        mul_le_mul_of_nonneg_left hg_ge (by positivity)
      have i3 : (n : ℝ) * L ^ 2 ≤ 2 * n ^ 2 * L ^ 2 := by
        have : (n : ℝ) ≤ 2 * n ^ 2 := by nlinarith
        exact mul_le_mul_of_nonneg_right this (sq_nonneg L)
      have h1 : (D + L) * L ≤ g ^ 2 := by
        have hD' : D = n * g + ((n : ℝ) - 1) * L := by linarith
        rw [hD']; linear_combination i1 + (1 / 2 : ℝ) * i2 + i3
      have h2 : A i * (L - c i) ≤ (D + L) * L :=
        mul_le_mul (hA_hi i) (by linarith) (by linarith) hDL.le
      linear_combination h2 + h1 + hsq
