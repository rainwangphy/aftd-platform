import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.WvgWins
import AFTD.Kb.GameTheoryEconomics.InStdSimplex
import AFTD.Kb.GameTheoryEconomics.IsOptimalBanzhafWeights
import AFTD.Kb.GameTheoryEconomics.Bz3Discr
import AFTD.Kb.GameTheoryEconomics.Bz3Check
import AFTD.Kb.GameTheoryEconomics.Bz3Coal
import AFTD.Kb.GameTheoryEconomics.Bz3Pattern
import AFTD.Kb.GameTheoryEconomics.Bz3Discrepancy
import AFTD.Kb.GameTheoryEconomics.Bz3PropsPattern

/-!
# banzhaf_strict_majority_veto_distortion_ge_five_thirds

Topic: general_equilibrium   Node: 8e7d8a7494a8

At simple majority with strict quota, the Banzhaf index has veto distortion at least 5/3: for target (3/10, 7/10, 0) the weights (1/2, 1/2, 0) are optimal and give player 0, whose target is 3/10, a veto.
-/

/-- **Veto distortion of Banzhaf power at simple majority with a strict quota is at least 5/3.** How Banzhaf Makes a Victor (EC 2026, Sec. 5) leaves open the case `q = 1/2` with strict quota and gives `veto-dist ≥ 6/5`. Here, for the Banzhaf index `β^{1/2}` (which at `q = 1/2` is also the adaptive Banzhaf index), the target `m = (3/10, 7/10, 0)` has the optimal weights `w* = (1/2, 1/2, 0)`, under which player 0 (`m₀ = 3/10`) holds a veto (`w*₀ ≥ 1 - q`). Hence `veto-dist_{1/2}(β^{1/2}) ≥ (1 - q)/m₀ = 5/3`. -/
theorem banzhaf_strict_majority_veto_distortion_ge_five_thirds :
    ∃ m w : Fin 3 → ℝ, in_std_simplex m ∧ is_optimal_banzhaf_weights m (1 / 2) (1 / 2) w ∧
      1 - 1 / 2 ≤ w 0 ∧ (1 - 1 / 2) / m 0 = 5 / 3 := by
  have hw : in_std_simplex ![1 / 2, 1 / 2, 0] := by
    refine ⟨fun i => by fin_cases i <;> norm_num, by simp [Fin.sum_univ_three]; norm_num⟩
  have hpat : bz3_pattern ![1 / 2, 1 / 2, 0] = ![false, false, false, true, false, false, false, true] := by
    funext k
    fin_cases k <;> simp [bz3_pattern, bz3_coal, wvg_wins, Finset.sum_insert]
  refine ⟨![3 / 10, 7 / 10, 0], ![1 / 2, 1 / 2, 0],
    ⟨fun i => by fin_cases i <;> norm_num, by simp [Fin.sum_univ_three]; norm_num⟩,
    ⟨hw, fun w' hw' => ?_⟩, by norm_num, by norm_num⟩
  rw [bz3_discrepancy, bz3_discrepancy, hpat]
  have hx : bz3_pattern w' = ![bz3_pattern w' 0, bz3_pattern w' 1, bz3_pattern w' 2,
      bz3_pattern w' 3, bz3_pattern w' 4, bz3_pattern w' 5, bz3_pattern w' 6, bz3_pattern w' 7] := by
    funext k; fin_cases k <;> rfl
  have hp := bz3_props_pattern w' hw'
  rw [hx] at hp ⊢
  have := bz3_check _ _ _ _ _ _ _ _ hp
  have h25 : bz3_discr ![false, false, false, true, false, false, false, true] = 2 / 5 := by
    decide +kernel
  rw [h25]
  exact_mod_cast this
