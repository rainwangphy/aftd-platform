import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RedistributionTradeError
import AFTD.Kb.GameTheoryEconomics.RedistributionShortfall
import AFTD.Kb.GameTheoryEconomics.RedistributionTrade

/-!
# trade_residual_error_round_one_tight

Topic: mechanism_design   Node: a5f5d2be6066

Provenance: original. Related work: arXiv:2610.10995 Remark 6.2

There exists a real constant c > 0 such that for every natural number n ≥ 3, there exists a profile θ : Fin n → ℝ with each θ i in [0, 1] and positive sum ∑ i, θ i > 0 such that c * (∑ i, θ i) / (n * (harmonic 1 : ℝ)) ≤ |redistribution_trade_error θ 1 (∑ i, θ i)|.
-/

lemma trade_residual_error_round_one_tight_sum_ite_ne (n : ℕ) (i₀ : Fin n) :
    ∑ k : Fin n, (if k = i₀ then (0 : ℝ) else 1) = n - 1 := by
  have : (fun k : Fin n => (if k = i₀ then (0 : ℝ) else 1)) =
      fun k => 1 - (if k = i₀ then 1 else 0) := by
    funext k
    split_ifs <;> ring
  rw [this, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp [Finset.sum_ite_eq']

lemma trade_residual_error_round_one_tight_sum_max_theta_sub (n : ℕ) (i₀ : Fin n) :
    let θ : Fin n → ℝ := fun i => if i = i₀ then 1 else 0
    ∑ j, ∑ k, max (θ j - θ k) 0 = (n - 1 : ℝ) := by
  intro θ
  have h_term (j k : Fin n) : max (θ j - θ k) 0 = if j = i₀ then (if k = i₀ then 0 else 1) else 0 := by
    dsimp [θ]
    by_cases hj : j = i₀ <;> by_cases hk : k = i₀ <;> simp [hj, hk]
  simp_rw [h_term]
  have h_inner (j : Fin n) : ∑ k, (if j = i₀ then (if k = i₀ then (0 : ℝ) else 1) else 0) =
      if j = i₀ then (n - 1 : ℝ) else 0 := by
    by_cases hj : j = i₀
    · simp [hj, trade_residual_error_round_one_tight_sum_ite_ne]
    · simp [hj]
  simp_rw [h_inner]
  simp [Finset.sum_ite_eq']

lemma trade_residual_error_round_one_tight_trade_shortfall_eq (n : ℕ) (i₀ : Fin n) :
    let θ : Fin n → ℝ := fun i => if i = i₀ then 1 else 0
    redistribution_trade θ redistribution_shortfall 1 = (n - 1 : ℝ) / (n : ℝ) ^ 2 := by
  intro θ
  dsimp [redistribution_trade, redistribution_shortfall]
  have h_simp (j k : Fin n) : (1 : ℝ) - (1 - θ j + θ k) = θ j - θ k := by ring
  simp_rw [h_simp]
  rw [trade_residual_error_round_one_tight_sum_max_theta_sub n i₀]
  ring

/-- Tightness of the harmonic residual error bound for m = 1 round of trade (OP-158 base case). -/
theorem trade_residual_error_round_one_tight :
    ∃ c > (0 : ℝ), ∀ (n : ℕ) (hn : 3 ≤ n),
      ∃ (θ : Fin n → ℝ) (hθ : ∀ i, θ i ∈ Set.Icc (0 : ℝ) 1) (hs : 0 < ∑ i, θ i),
        c * ((∑ i, θ i) / (n * (harmonic 1 : ℝ))) ≤
          |redistribution_trade_error θ 1 (∑ i, θ i)| := by
  use 1 / 2
  refine ⟨by norm_num, fun n hn => ?_⟩
  have hn_pos : 0 < n := by omega
  have hn_real : (3 : ℝ) ≤ n := by exact_mod_cast hn
  let i₀ : Fin n := ⟨0, hn_pos⟩
  let θ : Fin n → ℝ := fun i => if i = i₀ then 1 else 0
  have hθ : ∀ i, θ i ∈ Set.Icc (0 : ℝ) 1 := fun i => by
    dsimp [θ]
    split_ifs <;> simp
  have hs_val : ∑ i, θ i = 1 := by
    dsimp [θ]
    simp [Finset.sum_ite_eq']
  have hs : 0 < ∑ i, θ i := by
    rw [hs_val]
    norm_num
  refine ⟨θ, hθ, hs, ?_⟩
  rw [hs_val]
  have h_harm : (harmonic 1 : ℝ) = 1 := by simp [harmonic]
  rw [h_harm]
  have h_trade : redistribution_trade θ redistribution_shortfall 1 = (n - 1 : ℝ) / (n : ℝ) ^ 2 :=
    trade_residual_error_round_one_tight_trade_shortfall_eq n i₀
  have h_err : |redistribution_trade_error θ 1 1| = (n - 1 : ℝ) / (n : ℝ) ^ 2 := by
    change |redistribution_shortfall 1 - redistribution_trade θ redistribution_shortfall 1| = _
    have h_sf : redistribution_shortfall 1 = 0 := by simp [redistribution_shortfall]
    rw [h_sf, h_trade]
    simp only [zero_sub, abs_neg]
    rw [abs_of_nonneg]
    apply div_nonneg <;> nlinarith
  rw [h_err]
  have h_lhs : (1 : ℝ) / 2 * (1 / (↑n * 1)) = 1 / (2 * (n : ℝ)) := by ring
  rw [h_lhs]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith
