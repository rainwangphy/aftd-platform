import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Mnw2LbVal
import AFTD.Kb.GameTheoryEconomics.Mnw2LbIsMnw
import AFTD.Kb.GameTheoryEconomics.Mnw2LbMnwWelfare
import AFTD.Kb.GameTheoryEconomics.Mnw2LbOptWelfare
import AFTD.Kb.GameTheoryEconomics.IsMnwAllocation
import AFTD.Kb.GameTheoryEconomics.UtilitarianWelfare

/-!
# mnw_two_agents_price_lower_bound

Topic: fair_division   Node: 825a575b5e00

Provenance: formalization of a published result. Source: The Price of Fairness for Indivisible Goods, arXiv:1905.04910, Theorem 5.4 (for n = 2 the price of MNW is at least 27/23)

For every c < 27/23 there are two agents with additive, nonnegative, normalized valuations over three goods and an allocation O such that an MNW allocation exists and every MNW allocation N has c · SW(N) < SW(O). Together with the upper bound, the price of MNW and the strong price of MNW for two agents equal exactly 27/23. Instance: the lower-bound instance of arXiv:1905.04910 Theorem 5.4 with ε small, where SW(O)/SW(N) = (9/7)/(23/21 + ε) → 27/23.
-/

/-- The factor 27/23 is tight: for every c < 27/23 some normalized two-agent instance has an allocation whose welfare exceeds c times that of every MNW allocation. -/
theorem mnw_two_agents_price_lower_bound (c : ℝ) (hc : c < 27 / 23) : ∃ (m : ℕ) (v : Fin 2 → Fin m → ℝ) (O : Fin m → Fin 2), (∀ i g, 0 ≤ v i g) ∧ (∀ i, ∑ g, v i g = 1) ∧ (∃ N, is_mnw_allocation v N) ∧ ∀ N, is_mnw_allocation v N → c * utilitarian_welfare v N < utilitarian_welfare v O := by
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = 9 / 7 - c * (23 / 21) := ⟨_, rfl⟩
  have hd0 : 0 < d := by rw [hd]; linarith
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = min (1 / 14) (d / (2 * (|c| + 1))) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; exact lt_min (by norm_num) (div_pos hd0 (by positivity))
  have hε1 : ε < 1 / 7 := by rw [hε]; exact lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hε2 : ε ≤ d / (2 * (|c| + 1)) := by rw [hε]; exact min_le_right _ _
  have hcε : c * ε < d := by
    have h3 : c * ε ≤ |c| * ε := mul_le_mul_of_nonneg_right (le_abs_self c) hε0.le
    have h4 : ε * (2 * (|c| + 1)) ≤ d := (le_div_iff₀ (by positivity)).mp hε2
    nlinarith [abs_nonneg c]
  refine ⟨3, mnw2_lb_val ε, ![0, 0, 1], ?_, ?_, ⟨_, mnw2_lb_is_mnw ε hε0 hε1⟩, ?_⟩
  · intro i g
    fin_cases i <;> fin_cases g <;> simp [mnw2_lb_val] <;> linarith
  · intro i
    fin_cases i <;> simp [mnw2_lb_val, Fin.sum_univ_three] <;> ring
  · intro N hN
    rw [mnw2_lb_mnw_welfare ε hε0 hε1 N hN, mnw2_lb_opt_welfare ε]
    nlinarith
